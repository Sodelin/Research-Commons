#!/usr/bin/env python3
"""Bounded native private-word framing, refusal and UNKNOWN controls.

No coefficient oracle is duplicated here: design owns complete independent
arithmetic acceptance. This runner checks actual fresh process output against
frozen request inputs, including five explicitly unsupported completion cases.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import time

REPO = Path(__file__).resolve().parents[5]
PACKET = REPO / "research/2026-10-10-codex-lean-rust-parity"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def variables(request):
    source = request["context"]
    return [variable for slot in range(request["slots"])
            for variable in ([["X", slot, "E", edge] for edge in range(len(source["edges"]))]
                             + [["X", slot, "A", source["root"]]])] + [
        ["ORIGINAL_GAMMA", hybrid] for hybrid in range(len(source["hybrids"]))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--probe", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    origins = PACKET / "design/evidence/word-fixture-freeze-1"
    requests = {p.name.removesuffix(".request.json"): json.loads(p.read_bytes())
                for p in origins.glob("*.request.json")}
    require(len(requests) == 13, "Frozen request count changed")
    probe = args.probe.resolve()
    paths = [Path(__file__), probe, PACKET / "design/WORD-REFINEMENT.md",
             PACKET / "rust/notes/WORD-SOURCE-FREEZE-1.json",
             *sorted(origins.glob("*.request.json"))]
    before = {str(p): digest(p) for p in paths}
    results = []
    started = time.monotonic()

    def run(identifier, argv, request=None, status=None, limit=None, refusal=False):
        command = [str(probe), *argv]
        child = subprocess.run(command, capture_output=True, timeout=10, check=False)
        (args.output / (identifier + ".stdout")).write_bytes(child.stdout)
        (args.output / (identifier + ".stderr")).write_bytes(child.stderr)
        record = {"case": identifier, "command": command, "process_started": True,
                  "exit_code": child.returncode, "stdout_sha256": hashlib.sha256(child.stdout).hexdigest(),
                  "stderr_sha256": hashlib.sha256(child.stderr).hexdigest()}
        require(len(child.stdout) <= 4 * 1024 * 1024, "Native control frame exceeded 4MiB")
        if refusal:
            require(child.returncode == 2 and not child.stdout, "Invalid probe arguments promoted output")
            record["observed_status"] = "CLI_REFUSAL"
        else:
            require(child.returncode == 0, "Private probe process failed")
            actual = json.loads(child.stdout)
            common = {"schema": "source_word_probe_v1", "fixture": argv[0], "request": request,
                      "variables": variables(request), "source_admission_verified": False, "status": status}
            for key, value in common.items():
                require(actual.get(key) == value, "Native control field mismatch: " + key)
            require(actual["source_admission_verified"] is False, "Source gate promoted")
            if status == "UNSUPPORTED":
                require(set(actual) == set(common) | {"reason"}, "Unsupported result exposed a table")
                require(actual["reason"] == "SOURCE_WORD_ANCESTRAL_COMPLETION_NOT_EXTRACTED",
                        "Unsupported completion reason changed")
            elif status == "UNKNOWN":
                require(set(actual) == set(common) | {"limit"} and actual["limit"] == limit,
                        "UNKNOWN limits/framing changed or partial table exposed")
            else:
                require(set(actual) == set(common) | {"rows", "work"} and actual["rows"],
                        "Finite table framing changed")
                require(set(actual["work"]) == {"initial_assignments", "initial_term_contributions",
                        "queries", "branches", "term_products", "largest_row", "largest_terms"}
                        and all(type(n) is int and n >= 0 for n in actual["work"].values()),
                        "Logical work fields changed")
                record["rows"] = len(actual["rows"])
            record["observed_status"] = status
        record["status"] = "PASS"
        results.append(record)

    for name, request in sorted(requests.items()):
        run(name, [name], request, "TABLE" if request["terminal"] == "FULL_VIEW" else "UNSUPPORTED")
    controls = [("emptyNaturalWord", "initial_assignments", 1, "INITIAL", 2),
                ("emptyNaturalWord", "initial_terms", 2, "INITIAL", 3),
                ("conditionalCommonFalseWord", "queries", 0, 0, 1),
                ("conditionalCommonFalseWord", "branches", 0, 0, 1),
                ("conditionalCommonFalseWord", "term_products", 0, 0, 1),
                ("emptyConditionalWord", "destinations", 0, "INITIAL", 1),
                ("emptyConditionalWord", "terms", 0, "INITIAL", 1)]
    for name, kind, cap, stage, required in controls:
        request = copy.deepcopy(requests[name])
        request["limits"][kind] = cap
        run("unknown-" + kind, [name, "--limit", kind, str(cap)], request, "UNKNOWN",
            {"stage": stage, "kind": kind, "required": required, "cap": cap})
    for name, argv in [("missing-fixture", []), ("invalid-fixture", ["not-a-fixture"]),
                       ("invalid-count", ["emptyNaturalWord", "--limit", "queries", "bad"]),
                       ("invalid-limit", ["emptyNaturalWord", "--limit", "invented", "0"])]:
        run(name, argv, refusal=True)
    after = {str(p): digest(p) for p in paths}
    require(before == after, "Control/probe/request identity changed")
    receipt = {"schema": "rust_private_word_probe_controls_v1", "status": "PASS",
               "results": results, "case_count": len(results), "full_view_tables": 8,
               "unsupported_completion_cases": 5, "unknown_controls": 7, "cli_refusals": 4,
               "wall_seconds": time.monotonic() - started, "pins_before": before, "pins_after": after,
               "identities_stable": True, "source_admission_verified": False,
               "coefficient_oracle_acceptance_claimed": False, "original_lean_word_execution_claimed": False,
               "scope": "Actual private probe framing and refusal controls; mathematical coefficient acceptance is separate"}
    (args.output / "RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: receipt[k] for k in ("status", "case_count", "full_view_tables",
        "unsupported_completion_cases", "unknown_controls", "cli_refusals")}))


if __name__ == "__main__":
    main()
