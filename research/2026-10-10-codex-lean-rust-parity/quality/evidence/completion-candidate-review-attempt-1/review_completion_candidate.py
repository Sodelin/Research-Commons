#!/usr/bin/env python3
"""Authenticate the separately built completion candidate and captured checks."""
from datetime import datetime, timezone
import json
from pathlib import Path

from review_word_candidate import PACKET, ROOT, check_witness, coefficients, digest, read


def main():
    errors, pins, tables = [], {}, []

    def authenticate(path, expected):
        observed = digest(path)
        pins[str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)] = observed
        if observed != expected:
            errors.append("Identity: " + str(path))

    frozen = PACKET / "rust/evidence/history/word-completion-candidate-v1"
    snapshot = read(frozen / "SNAPSHOT.json")
    freeze_path = PACKET / "rust/notes/WORD-COMPLETION-SOURCE-FREEZE-1.json"
    freeze = read(freeze_path)
    build_dir = PACKET / "rust/evidence/word-completion-build-1"
    build = read(build_dir / "BUILD-RECEIPT.json")
    authenticate(freeze_path, build["freeze_sha256"])
    for row in snapshot["files"]:
        authenticate(frozen / row["path"], row["sha256"])
    for row in snapshot["binaries"]:
        authenticate(Path(row["preserved_path"]), row["sha256"])
    compile_count = 0
    for row in freeze["inputs"]:
        if row["role"] == "compile_input":
            compile_count += 1
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
            or compile_count != 28 or len(snapshot["files"]) != 44
            or build["source_admission_claim"] or build["general_word_refinement_proof_claim"]
            or build["public_runtime_replaced"] or not freeze["terminal_completion_implemented"]):
        errors.append("Completion build scope/binding")

    evidence = PACKET / "design/evidence/word-completion-rust-review-1"
    comparison = read(evidence / "RECEIPT.json")
    if (comparison["status"] != "PASS" or not comparison["stable"]
            or comparison["pins_before"] != comparison["pins_after"]
            or comparison["controls_total"] != 20 or len(comparison["results"]) != 20
            or comparison["actual_lean_execution"] or comparison["generic_native_refinement_proved"]
            or comparison["source_admission_verified"]
            or comparison["pins_before"].get(build["source_word_probe"]) != build["source_word_probe_sha256"]):
        errors.append("Comparison scope/build binding")
    for path, expected in comparison["pins_before"].items():
        authenticate(Path(path), expected)
    statuses = {}
    for result in comparison["results"]:
        name = result["control"]
        expected_path = evidence / (name + ".expected.json")
        actual_path = evidence / (name + ".rust.stdout")
        expected, actual = read(expected_path), read(actual_path)
        status = expected["status"]
        statuses[status] = statuses.get(status, 0) + 1
        try:
            if (result["status"] != "PASS" or not result["process_started"]
                    or result["exit_code"] != (1 if status == "REFUSED" else 0)
                    or (evidence / (name + ".rust.stderr")).read_bytes()
                    or set(actual) != set(expected)
                    or any(actual[field] != expected[field] for field in set(expected) - {"rows"})):
                raise ValueError("Captured control/status/frame/work differs")
            if status == "TABLE":
                if coefficients(actual["rows"]) != coefficients(expected["rows"]):
                    raise ValueError("Complete coefficients or destinations differ")
                for row in actual["rows"]:
                    check_witness(row)
                    witness = row["witness"]
                    if len(witness["live"]) != 1:
                        raise ValueError("Completion has multiple owners")
                    if any(place != ["A", actual["request"]["context"]["original"]["root"]]
                           for place in row["view"]["location"]):
                        raise ValueError("Completion leaves original root")
                tables.append({"fixture": name, "full_rows": len(actual["rows"]),
                               "terms": sum(len(row["coefficients"]) for row in actual["rows"])})
        except (ValueError, KeyError, TypeError) as error:
            errors.append(name + ": " + str(error))
        for path in (expected_path, actual_path):
            pins[str(path.relative_to(ROOT))] = digest(path)
    if statuses != {"TABLE": 11, "UNKNOWN": 5, "REFUSED": 4} or sum(row["full_rows"] for row in tables) != 330:
        errors.append("Exact completion control/table counts")

    regression_path = PACKET / "design/evidence/word-completion-candidate-regression-1/PARITY-RECEIPT.json"
    regression = read(regression_path)
    if (not regression["pass"] or regression["cases_passed"] != 117 or regression["cases_total"] != 117
            or len(regression["cases"]) != 117 or not regression["identities"]["identities_stable"]
            or regression["identities"]["executables"]["rust"]["sha256"] != build["binary_sha256"]):
        errors.append("Fresh117 protocol candidate binding")
    expected_exits = {"SAT": 0, "UNSAT": 0, "TABLE": 0, "UNKNOWN": 2,
                      "CONDITIONAL_ARITHMETIC": 2, "REFUSED": 1}
    for case in regression["cases"]:
        if (not case["pass"] or case["errors"]
                or any(status != case["expected"] for status in case["status"].values())
                or any(run["exit_code"] != expected_exits[case["expected"]] for run in case["runs"].values())):
            errors.append("Protocol case: " + case["name"])

    finite_cases = 0
    for name, old_name, required in (("word-completion-finite-regression-1", "word-rust-review-1", 8),
                                    ("word-completion-finite-hybrid-regression-1", "word-hybrid-rust-review-1", 2)):
        evidence = PACKET / "design/evidence" / name
        receipt = read(evidence / "RECEIPT.json")
        if (receipt["status"] != "PASS" or not receipt["stable"] or len(receipt["results"]) != required
                or receipt["pins_before"] != receipt["pins_after"]
                or receipt["pins_before"].get(build["source_word_probe"]) != build["source_word_probe_sha256"]):
            errors.append("Finite compatibility receipt: " + name)
        for result in receipt["results"]:
            fixture = result["fixture"]
            expected = read(evidence / (fixture + ".expected.json"))
            actual = read(evidence / (fixture + ".rust.stdout"))
            previous = read(PACKET / "design/evidence" / old_name / (fixture + ".expected.json"))
            if (expected != previous or result["status"] != "PASS" or result["exit_code"] != 0
                    or coefficients(actual["rows"]) != coefficients(expected["rows"])
                    or any(actual[field] != expected[field] for field in set(expected) - {"rows"})):
                errors.append("Finite compatibility full table: " + fixture)
            for row in actual["rows"]:
                check_witness(row)
            finite_cases += 1
    receipt = {
        "schema": "ancestral_completion_saved_candidate_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
        "errors": errors, "tables": tables, "status_counts": statuses,
        "finite_compatibility_cases": finite_cases, "authenticated_artifacts": len(pins), "pins": pins,
        "comparison_sha256": digest(PACKET / "design/evidence/word-completion-rust-review-1/RECEIPT.json"),
        "build_sha256": digest(build_dir / "BUILD-RECEIPT.json"),
        "regression_sha256": digest(regression_path), "reviewer_sha256": digest(Path(__file__)),
        "helpers": {name: digest(Path(__file__).with_name(name)) for name in ("review_word_candidate.py",)},
        "scope": "Saved original-source-bound completion candidate:11 complete tables330 ordered views,5 UNKNOWNs,4 refusals,10 unchanged finite cases and fresh117 protocol receipt. Exact source/build/frozen runtime identities and complete coefficient/work/witness reconstruction checked; no new execution, compiled Lean completion acceptance or generic native refinement inferred.",
    }
    (PACKET / "quality/COMPLETION-CANDIDATE-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ("pass", "errors", "status_counts", "finite_compatibility_cases", "authenticated_artifacts")}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
