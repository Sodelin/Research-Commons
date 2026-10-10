#!/usr/bin/env python3
"""Review preserved actual-boundary kernel audits and evaluator receipt bindings."""
from datetime import datetime, timezone
import json
from pathlib import Path

from review_proof_extensions import review
from review_support_join import PACKET, identity, read


def main():
    proof = review("ORIGINAL-BOUNDARY-FIXTURE", {
        "G7OriginalBoundaryFixture": (157, 4913, 2873),
        "G7OriginalBoundaryFixtureMain": (158, 4914, 2873)},
        {"cache_reuse": 313, "fresh_components": 2})
    execution_path = PACKET / "lean/ORIGINAL-BOUNDARY-NATIVE-EXECUTION-RESULT.json"
    execution = read(execution_path)
    certificate = read(PACKET / "lean/ORIGINAL-BOUNDARY-FIXTURE-CERTIFICATE.json")
    comparison_path = Path(execution["coefficient_review_evidence"]) / "RECEIPT.json"
    comparison = read(comparison_path)
    checks = {
        "kernel_fixture_audits": proof["pass"],
        "actual_execution": execution["status"] == "PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL"
            and execution["exit_code"] == 0 and execution["fixtures_total"] == execution["fixtures_passed"] == 12,
        "complete_imported_artifacts_stable": execution["all_actual_imported_artifacts_compiler_and_native_libraries_final_stable"],
        "same_kernel_evidence": execution["kernel_evidence"] == certificate["evidence"],
        "exact_comparison_binding": identity(comparison_path)["sha256"] == execution["coefficient_review_receipt_sha256"],
        "no_standalone_or_gate_promotion": not execution["standalone_elf_claimed"]
            and not execution["general_Rust_refinement_claimed"]
            and not execution["scientific_provider_gates_promoted"],
    }
    errors = proof["errors"] + [key for key, passed in checks.items() if not passed]
    receipt = {
        "schema": "actual_boundary_fixture_saved_evidence_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
        "errors": errors, "checks": checks, "proof": proof,
        "execution": identity(execution_path), "comparison": identity(comparison_path),
        "comparison_schema": comparison["schema"],
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helpers": {name: identity(Path(__file__).with_name(name)) for name in
                    ("review_proof_extensions.py", "review_support_join.py")},
        "scope": "Exact saved157/158 ownership audits, actual12-context evaluator acceptance and comparison artifact bindings. No new compiler/evaluator run or generic native refinement; independent coefficient recheck remains the separately saved design review.",
    }
    (PACKET / "quality/BOUNDARY-FIXTURE-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": errors}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
