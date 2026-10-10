#!/usr/bin/env python3
"""Review preserved original word audits and actual evaluator bindings."""
from datetime import datetime, timezone
from pathlib import Path
import json

from review_proof_extensions import review
from review_support_join import PACKET, identity, read


def main():
    proof = review("ORIGINAL-WORD-FIXTURE", {
        "G7OriginalWordFixture": (171, 5287, 3078),
        "G7OriginalWordFixtureMain": (172, 5288, 3078)},
        {"cache_reuse": 341, "fresh_components": 2})
    execution_path = PACKET / "lean/ORIGINAL-WORD-NATIVE-EXECUTION-RESULT.json"
    execution = read(execution_path)
    certificate = read(PACKET / "lean/ORIGINAL-WORD-FIXTURE-CERTIFICATE.json")
    comparison_path = Path(execution["coefficient_review_evidence"]) / "RECEIPT.json"
    comparison = read(comparison_path)
    checks = {
        "kernel_fixture_audits": proof["pass"],
        "actual_execution": execution["status"] == "PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL"
            and execution["exit_code"] == 0
            and execution["fixtures_total"] == execution["fixtures_passed"] == 9,
        "complete_rows_and_adversarial_controls": execution["full_view_rows_total"]
            == comparison["full_view_rows_total"] == 39
            and len(execution["invalid_table_controls_rejected"]) == 8
            and execution["invalid_table_controls_rejected"]
            == comparison["invalid_table_controls_rejected"],
        "both_languages_and_all_cases_pass": comparison["pass"]
            and comparison["cases_total"] == comparison["cases_passed"] == 9
            and set(execution["languages_executed"]) == set(comparison["languages_executed"])
            == {"rust", "lean"}
            and len(comparison["cases"]) == 9
            and all(case["pass"] and not case["errors"]
                    and set(case["runs"]) == {"rust", "lean"}
                    and all(run["process_started"] and run["exit_code"] == 0
                            and not run["timed_out"]
                            and run["coefficient_review"]["status"] == "PASS"
                            for run in case["runs"].values())
                    for case in comparison["cases"]),
        "complete_imported_artifacts_stable": execution[
            "all_actual_imported_artifacts_compiler_and_native_libraries_final_stable"],
        "same_kernel_evidence": execution["kernel_evidence"] == certificate["evidence"],
        "exact_comparison_binding": identity(comparison_path)["sha256"]
            == execution["coefficient_review_receipt_sha256"],
        "same_current_comparator": identity(PACKET / "design/review_word_compiled_fixtures.py")["sha256"]
            == execution["design_review_script_sha256"],
        "no_standalone_or_gate_promotion": not execution["standalone_elf_claimed"]
            and not execution["general_Rust_refinement_claimed"]
            and not execution["scientific_provider_gates_promoted"],
    }
    errors = proof["errors"] + [key for key, passed in checks.items() if not passed]
    receipt = {
        "schema": "actual_word_fixture_saved_evidence_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "checks": checks, "proof": proof,
        "execution": identity(execution_path), "comparison": identity(comparison_path),
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helpers": {name: identity(Path(__file__).with_name(name)) for name in
                    ("review_proof_extensions.py", "review_support_join.py")},
        "scope": "Saved171/172 complete ownership audits and actual nine-context Lean/Rust evaluator comparison covering39 ordered rows and eight adversarial table controls. No new compiler/evaluator run, generic native refinement, calendar admission or master closure inferred. Independent saved coefficient replay is a separate design receipt.",
    }
    (PACKET / "quality/WORD-FIXTURE-REVIEW.json").write_text(
        json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": errors,
                      "preserved_artifacts": proof["preserved_artifacts"]}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
