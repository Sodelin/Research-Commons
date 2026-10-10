#!/usr/bin/env python3
"""Review saved boundary build/finite comparison evidence against frozen inputs."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    errors = []
    frozen = PACKET / "rust/evidence/history/boundary-v1"
    snapshot = read(frozen / "SNAPSHOT.json")
    freeze_path = PACKET / "rust/notes/BOUNDARY-SOURCE-FREEZE-1.json"
    freeze = read(freeze_path)
    build = read(PACKET / "rust/evidence/boundary-build-1/BUILD-RECEIPT.json")
    comparison = read(PACKET / "design/evidence/boundary-rust-review-1/RECEIPT.json")
    regression = read(PACKET / "design/evidence/boundary-candidate-regression-1/PARITY-RECEIPT.json")
    compile_count = 0
    for row in snapshot["files"]:
        if digest(frozen / row["path"]) != row["sha256"]:
            errors.append("Frozen source: " + row["path"])
    for row in freeze["inputs"]:
        if row["role"] == "compile_input":
            compile_count += 1
            suffix = Path(row["path"]).relative_to(PACKET.relative_to(ROOT) / "rust")
            path = frozen / suffix
        else:
            path = ROOT / row["path"]
        if digest(path) != row["sha256"]:
            errors.append("Build input: " + row["path"])
    for row in freeze["inherited_providers"]:
        if digest(ROOT / row["path"]) != row["sha256"]:
            errors.append("Inherited provider: " + row["path"])
    for row in snapshot["binaries"]:
        if digest(Path(row["preserved_path"])) != row["sha256"]:
            errors.append("Preserved runtime: " + row["role"])
    for row in build["commands"]:
        if row["exit_code"] != 0 or row["timed_out"] or not row["process_started"]:
            errors.append("Build process: " + row["id"])
    evidence = PACKET / "design/evidence/boundary-rust-review-1"
    for case in comparison["cases"]:
        run = case["runs"]["rust"]
        if not case["pass"] or case["errors"] or run["exit_code"] != 0:
            errors.append("Boundary case: " + case["fixture"])
        for stream in ("stdout", "stderr"):
            captured = evidence / (case["fixture"] + ".rust." + stream)
            expected = run.get(stream + "_sha256")
            if (expected is not None and digest(captured) != expected) or (expected is None and captured.read_bytes()):
                errors.append("Boundary captured stream: " + case["fixture"] + "/" + stream)
    for case in regression["cases"]:
        expected_exit = {"SAT": 0, "UNSAT": 0, "TABLE": 0, "UNKNOWN": 2,
                         "CONDITIONAL_ARITHMETIC": 2, "REFUSED": 1}[case["expected"]]
        if (not case["pass"] or case["errors"]
                or any(status != case["expected"] for status in case["status"].values())
                or any(run["exit_code"] != expected_exit for run in case["runs"].values())):
            errors.append("Protocol regression: " + case["name"])
    checks = {
        "exact_build_freeze": digest(freeze_path) == build["freeze_sha256"] and freeze == build["frozen_inputs"],
        "build_pass_stable": build["status"] == "PASS" and build["compile_input_rehash_stable"]
                             and build["preserved_runtime_rehash_stable"],
        "exact_compile_carrier": compile_count == 23 and len(snapshot["files"]) == 32,
        "all_boundary_cases": comparison["pass"] and comparison["cases_total"] == comparison["cases_passed"] == len(comparison["cases"]) == 12,
        "comparison_pins_stable": comparison["binary_pins_before"] == comparison["binary_pins_after"]
                                  == {"rust": build["source_boundary_probe_sha256"]}
                                  and comparison["source_pins_before"] == comparison["source_pins_after"],
        "all_protocol_cases": regression["pass"] and regression["cases_total"] == regression["cases_passed"] == len(regression["cases"]) == 117,
        "protocol_candidate_binding": regression["identities"]["identities_stable"]
                                      and regression["identities"]["executables"]["rust"]["sha256"] == build["binary_sha256"],
        "asymmetric_control": comparison["controls"]["asymmetric_gamma"] == "1/3"
                              and comparison["controls"]["required_LAW_G"] == "2/3"
                              and comparison["controls"]["wrong_direct_gamma_binding_rejected"],
        "no_gate_promotion": not build["source_admission_claim"] and not build["public_runtime_replaced"]
                             and not build["general_boundary_refinement_proof_claim"]
                             and not comparison["general_refinement_proof_claim"],
    }
    errors.extend(key for key, passed in checks.items() if not passed)
    receipt = {"schema": "boundary_saved_candidate_identity_review_v1",
               "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
               "errors": errors, "checks": checks, "frozen_snapshot_sha256": digest(frozen / "SNAPSHOT.json"),
               "build_sha256": digest(PACKET / "rust/evidence/boundary-build-1/BUILD-RECEIPT.json"),
               "comparison_sha256": digest(evidence / "RECEIPT.json"),
               "reviewer_sha256": digest(Path(__file__)),
               "scope": "Saved finite build/independent comparison/source and preserved runtime identity review. Current additive word drafts are not part of this frozen build. No new native run, typed baseline acceptance, universal refinement or master completion."}
    (PACKET / "quality/BOUNDARY-CANDIDATE-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": errors, "compile_inputs": compile_count}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
