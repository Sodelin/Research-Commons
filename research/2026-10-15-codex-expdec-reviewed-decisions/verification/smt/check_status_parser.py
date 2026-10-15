#!/usr/bin/env python3
"""Regression controls for evidence classification, without solver execution."""

import argparse
import hashlib
import json
from pathlib import Path

from run_checks import classify_result


BASE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    # These strings are parser fixtures, not claimed native solver receipts.
    fixtures = [
        ("unknown-clean", "unknown\n", 0, False, "", "unknown", "unknown", False),
        ("unknown-proof-unavailable", 'unknown\n(error "proof is not available")\n', 0, False, "", "unknown", "unknown", True),
        ("unknown-model-unavailable-stderr", "unknown\n", 0, False, 'Error: model is not available\n', "unknown", "unknown", True),
        ("sat-model-unavailable", 'sat\n(error "model is not available")\n', 0, False, "", "ARTIFACT_FAILURE", "sat", True),
        ("unsat-proof-unavailable", 'unsat\n(error "proof is not available")\n', 0, False, "", "ARTIFACT_FAILURE", "unsat", True),
        ("duplicate-status", "unsat\nunsat\n", 0, False, "", "INVALID_SOLVER_OUTPUT", None, False),
        ("conflicting-status", "sat\nunsat\n", 0, False, "", "INVALID_SOLVER_OUTPUT", None, False),
        ("missing-status", '(error "invalid command")\n', 0, False, "", "INVALID_SOLVER_OUTPUT", None, False),
        ("nonzero-exit-preserves-unknown", 'unknown\n(error "proof is not available")\n', 1, False, "", "EXECUTION_FAILURE", "unknown", True),
        ("timeout-preserves-unknown", "unknown\n", -9, True, "", "WALL_TIMEOUT", "unknown", False),
        ("syntax-error-not-artifact", 'unknown\n(error "invalid command")\n', 0, False, "", "INVALID_SOLVER_OUTPUT", "unknown", False),
        ("clean-unsat", "unsat\n(proof (asserted false))\n", 0, False, "", "unsat", "unsat", False),
        ("clean-sat", "sat\n((x 0.0))\n", 0, False, "", "sat", "sat", False),
    ]
    results = []
    for name, raw, code, timeout, stderr, actual, status, artifact in fixtures:
        result = classify_result(raw, code, timeout, stderr)
        valid = (result["actual"] == actual and result["solver_status"] == status
                 and result["artifact_error"] == artifact
                 and result["usable_decision_evidence"] == (actual in ("sat", "unsat")))
        results.append({"name": name, "fixture_kind": "synthetic parser regression",
                        "stdout": raw, "stderr": stderr, "exit_code": code,
                        "wall_timeout": timeout, "classification": result,
                        "expected_actual": actual, "valid": valid})
    retained_receipt = BASE / "results/20261015-run-02/RESULT.json"
    retained = json.loads(retained_receipt.read_text())
    replays = []
    for result in retained["results"]:
        stdout = retained_receipt.parent / result["stdout"]
        stderr = retained_receipt.parent / result["stderr"]
        if digest(stdout) != result["stdout_sha256"] or digest(stderr) != result["stderr_sha256"]:
            raise ValueError("retained output hash mismatch")
        classified = classify_result(stdout.read_text(), result["exit_code"],
                                     result["wall_timeout"], stderr.read_text())
        replays.append({"id": result["id"], "old_actual": result["actual"],
                        "classification": classified,
                        "unchanged": classified["actual"] == result["actual"]})
    document = {"schema": "expdec-status-parser-regression-v1",
                "checker_sha256": digest(Path(__file__)),
                "parser_source_sha256": digest(BASE / "run_checks.py"),
                "retained_receipt_sha256": digest(retained_receipt),
                "native_solver_executed": False,
                "fixtures": results, "retained_output_replays": replays,
                "all_valid": all(r["valid"] for r in results) and all(r["unchanged"] for r in replays)}
    with args.output.open("x") as output:
        json.dump(document, output, indent=2, sort_keys=True)
        output.write("\n")
    print(json.dumps({"parser_fixtures": len(results), "retained_output_replays": len(replays),
                      "all_valid": document["all_valid"]}))
    if not document["all_valid"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
