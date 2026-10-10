#!/usr/bin/env python3
"""Authenticate preserved finite-word builds and independently reread full tables.

This reviews captured evidence; it does not execute Rust, Lean or the oracle.
"""
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def key(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def coefficients(rows):
    result = {}
    for row in rows:
        view = key(row["view"])
        if view in result:
            raise ValueError("Duplicate selected destination")
        polynomial = {}
        for powers, raw in row["coefficients"]:
            power = tuple(powers)
            value = Fraction(raw)
            if power in polynomial or not value or any(type(p) is not int or p < 0 for p in power):
                raise ValueError("Noncanonical coefficient")
            polynomial[power] = value
        result[view] = polynomial
    return result


def leaves(tree):
    if type(tree) is int:
        return [tree]
    if type(tree) is not list or len(tree) != 2:
        raise ValueError("Malformed ordered genealogy")
    return leaves(tree[0]) + leaves(tree[1])


def check_witness(row):
    """Reconstruct the complete selected fibre from its literal retained state."""
    witness, view = row["witness"], row["view"]
    count = len(witness["ancestor"])
    if any(len(witness[field]) != count for field in ("genealogy", "location")):
        raise ValueError("Literal carrier dimensions")
    owners = set(witness["live"])
    if len(owners) != len(witness["live"]) or any(type(i) is not int or not 0 <= i < count for i in owners):
        raise ValueError("Literal live-owner registry")
    for owner in range(count):
        if owner in owners:
            if witness["ancestor"][owner] != owner:
                raise ValueError("Owner is not its ancestor")
            fibre = [i for i, ancestor in enumerate(witness["ancestor"]) if ancestor == owner]
            if sorted(leaves(witness["genealogy"][owner])) != fibre:
                raise ValueError("Genealogy does not cover its exact copy fibre")
            if witness["location"][owner] is None:
                raise ValueError("Live owner lacks actual population")
        elif witness["genealogy"][owner] is not None or witness["location"][owner] is not None:
            raise ValueError("Dead owner retains literal coordinates")
    if any(owner not in owners for owner in witness["ancestor"]):
        raise ValueError("Copy has no live ancestor")
    expected = {
        "genealogy": [witness["genealogy"][owner] for owner in witness["ancestor"]],
        "location": [witness["location"][owner] for owner in witness["ancestor"]],
        "register": witness["register"],
    }
    if expected != view:
        raise ValueError("Full selected view differs from literal witness")


def main():
    errors, pins, checked = [], {}, []

    def authenticate(path, expected):
        actual = digest(path)
        pins[str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)] = actual
        if actual != expected:
            errors.append("Identity: " + str(path))

    builds = []
    for version, history in ((1, "word-v1"), (2, "word-finite-v2")):
        frozen = PACKET / "rust/evidence/history" / history
        snapshot = read(frozen / "SNAPSHOT.json")
        freeze_path = PACKET / f"rust/notes/WORD-SOURCE-FREEZE-{version}.json"
        freeze = read(freeze_path)
        build_dir = PACKET / f"rust/evidence/word-build-{version}"
        build = read(build_dir / "BUILD-RECEIPT.json")
        authenticate(freeze_path, build["freeze_sha256"])
        for row in snapshot["files"]:
            authenticate(frozen / row["path"], row["sha256"])
        for row in snapshot["binaries"]:
            authenticate(Path(row["preserved_path"]), row["sha256"])
        compile_inputs = 0
        for row in freeze["inputs"]:
            if row["role"] == "compile_input":
                compile_inputs += 1
                suffix = Path(row["path"]).relative_to(PACKET.relative_to(ROOT) / "rust")
                path = frozen / suffix
            else:
                path = ROOT / row["path"]
            authenticate(path, row["sha256"])
        for row in freeze["inherited_providers"]:
            authenticate(ROOT / row["path"], row["sha256"])
        for command in build["commands"]:
            if command["exit_code"] != 0 or command["timed_out"] or not command["process_started"]:
                errors.append("Build command: " + command["id"])
            for stream in ("stdout", "stderr"):
                authenticate(build_dir / (command["id"] + "." + stream), command[stream + "_sha256"])
        if (build["status"] != "PASS" or not build["compile_input_rehash_stable"]
                or not build["preserved_runtime_rehash_stable"] or freeze != build["frozen_inputs"]
                or compile_inputs != 26 or build["source_admission_claim"]
                or build["general_word_refinement_proof_claim"] or build["public_runtime_replaced"]):
            errors.append("Build scope/identity: " + str(version))
        builds.append(build)

    for name, expected_count, build in (("word-rust-review-1", 8, builds[0]),
                                       ("word-hybrid-rust-review-1", 2, builds[1])):
        evidence = PACKET / "design/evidence" / name
        receipt = read(evidence / "RECEIPT.json")
        if (receipt["status"] != "PASS" or not receipt["stable"]
                or receipt["pins_before"] != receipt["pins_after"]
                or len(receipt["results"]) != expected_count or receipt["actual_lean_execution"]
                or receipt["source_admission_verified"]):
            errors.append("Comparison scope: " + name)
        if receipt["pins_before"].get(build["source_word_probe"]) != build["source_word_probe_sha256"]:
            errors.append("Comparison build binding: " + name)
        for result in receipt["results"]:
            fixture = result["fixture"]
            expected_path = evidence / (fixture + ".expected.json")
            actual_path = evidence / (fixture + ".rust.stdout")
            expected, actual = read(expected_path), read(actual_path)
            try:
                if (result["status"] != "PASS" or result["exit_code"] != 0
                        or actual["status"] != "TABLE" or expected["status"] != "TABLE"
                        or coefficients(actual["rows"]) != coefficients(expected["rows"])
                        or any(actual[field] != expected[field] for field in set(expected) - {"rows"})
                        or len(actual["rows"]) != result["full_view_rows"]
                        or (evidence / (fixture + ".rust.stderr")).read_bytes()):
                    raise ValueError("Captured full table or exact work differs")
                for row in actual["rows"]:
                    check_witness(row)
            except (ValueError, KeyError, TypeError) as error:
                errors.append(f"Fixture {fixture}: {error}")
            for path in (expected_path, actual_path):
                pins[str(path.relative_to(ROOT))] = digest(path)
            checked.append({"fixture": fixture, "full_rows": len(actual["rows"]),
                            "terms": sum(len(row["coefficients"]) for row in actual["rows"])})

    regression_path = PACKET / "design/evidence/word-candidate-regression-1/PARITY-RECEIPT.json"
    regression = read(regression_path)
    if (not regression["pass"] or regression["cases_passed"] != 117 or regression["cases_total"] != 117
            or len(regression["cases"]) != 117
            or not regression["identities"]["identities_stable"]
            or regression["identities"]["executables"]["rust"]["sha256"] != builds[0]["binary_sha256"]
            or builds[0]["binary_sha256"] != builds[1]["binary_sha256"]):
        errors.append("Preserved117 protocol identity")
    expected_exits = {"SAT": 0, "UNSAT": 0, "TABLE": 0, "UNKNOWN": 2,
                      "CONDITIONAL_ARITHMETIC": 2, "REFUSED": 1}
    for case in regression["cases"]:
        if (not case["pass"] or case["errors"]
                or any(status != case["expected"] for status in case["status"].values())
                or any(run["exit_code"] != expected_exits[case["expected"]] for run in case["runs"].values())):
            errors.append("Protocol case: " + case["name"])
    receipt = {
        "schema": "word_saved_candidate_identity_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
        "errors": errors, "fixtures": checked, "full_tables_checked": len(checked),
        "full_rows_checked": sum(row["full_rows"] for row in checked),
        "authenticated_artifacts": len(pins), "pins": pins,
        "regression_receipt_sha256": digest(regression_path),
        "reviewer_sha256": digest(Path(__file__)),
        "scope": "Preserved finite8+2 full coefficient tables, exact logical work, literal range-witness reconstruction, frozen build/source/native identities and117 protocol receipt. No new execution, generic native refinement, completion or master closure.",
    }
    (PACKET / "quality/WORD-CANDIDATE-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ("pass", "errors", "full_tables_checked", "full_rows_checked", "authenticated_artifacts")}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
