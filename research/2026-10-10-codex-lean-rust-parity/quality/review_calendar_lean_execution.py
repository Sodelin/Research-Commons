#!/usr/bin/env python3
"""Review actual saved Lean evaluations without launching either solver."""
import json
from datetime import datetime, timezone
from pathlib import Path

from review_support_join import PACKET, identity, read


def main():
    result_path = PACKET / "lean/ORIGINAL-CALENDAR-LEAN-EVALUATOR-RESULT.json"
    result = read(result_path)
    evidence = PACKET / "lean" / result["evidence"]
    receipt_path = evidence / "RECEIPT.json"
    receipt = read(receipt_path)
    qualifier = read(evidence / "EXECUTION-QUALIFICATION.json")
    preservation_path = evidence / "PRESERVATION-MANIFEST.json"
    preservation = read(preservation_path)
    config = read(evidence / "LEAN-EXECUTION-CONFIG.json")
    proof = read(PACKET / "quality/CALENDAR-FIXTURE-PROOF-REVIEW.json")
    errors = []
    for row in preservation["files"]:
        if identity(evidence / row["path"]) != {k: row[k] for k in ("sha256", "bytes")}:
            errors.append("preserved: " + row["path"])
    for path, digest in receipt["pins_after"].items():
        if identity(Path(path))["sha256"] != digest:
            errors.append("current pinned artifact: " + path)
    expected = {"twoTipCalendar": (2, 2), "serialNegativeTips": (12, 16),
                "parallelCommonCalendar": (24, 48)}
    for case in receipt["cases"]:
        name = case["fixture"]
        run = case["runs"]["lean"]
        counts = (case["full_view_rows"], run["coefficient_review"]["terms"])
        valid = (name in expected and counts == expected[name] and case["pass"]
                 and not case["errors"] and set(case["runs"]) == {"lean"}
                 and run["process_started"] and run["exit_code"] == 0
                 and not run["timed_out"] and run["coefficient_review"]["status"] == "PASS"
                 and run["command"][0] == config["compiler_path"]
                 and "-t0" in run["command"]
                 and "-Ddebug.skipKernelTC=false" in run["command"])
        for suffix in ("stdout", "stderr"):
            valid &= identity(evidence / (name + ".lean." + suffix))["sha256"] == run[suffix + "_sha256"]
        if not valid:
            errors.append("actual bounded Lean case: " + name)
    checks = {
        "checked_fixture_source": proof["pass"] and not proof["errors"],
        "same_kernel_certificate": identity(Path(result["compiler_kernel_fixture_certificate"]))["sha256"]
            == result["compiler_kernel_fixture_certificate_sha256"] == proof["proof"]["certificate"]["sha256"],
        "same_kernel_evidence": receipt["separately_authenticated_kernel_evidence"] == config["kernel_evidence"]
            == read(PACKET / "lean/ORIGINAL-CALENDAR-FIXTURE-CERTIFICATE.json")["evidence"],
        "saved_comparison_binding": identity(receipt_path)["sha256"] == result["driver_receipt_sha256"]
            == qualifier["driver_receipt_sha256"] == preservation["unchanged_driver_receipt_sha256"],
        "complete_preservation": len(preservation["files"]) == result["preserved_output_files"] == 30
            and identity(preservation_path)["sha256"] == result["preservation_manifest_sha256"],
        "complete_actual_cases": receipt["pass"] and receipt["cases_total"] == receipt["cases_passed"] == 3
            and len(receipt["cases"]) == 3 and {c["fixture"] for c in receipt["cases"]} == set(expected)
            and receipt["full_view_rows_total"] == result["full_view_rows"] == 38
            and receipt["languages_executed"] == ["lean"]
            and result["compiled_lean_evaluator_processes"] == 3 and result["new_native_calendar_processes"] == 0,
        "stable_pins": receipt["pins_before"] == receipt["pins_after"],
        "adversarial_controls": len(receipt["invalid_table_controls_rejected"]) == 8
            and receipt["invalid_table_controls_rejected"] == read(PACKET /
                "design/evidence/calendar-original-reference-preparation-1/RECEIPT.json")["invalid_table_controls_rejected"],
        "scope_qualification": result["driver_phase_permutation_qualification_does_not_establish_specific_instances"]
            and not result["specific_literal_phase_or_physical_PMF_instances_accepted"]
            and not qualifier["specific_literal_phase_or_physical_PMF_instances_accepted"]
            and not receipt["Lean_native_work_counters_inferred"]
            and not receipt["Lean_standalone_ELF_claim"]
            and not receipt["general_native_calendar_refinement_claim"]
            and not receipt["source_admission_verified"],
    }
    errors.extend(name for name, passed in checks.items() if not passed)
    answer = {
        "schema": "original_completed_literal_word_actual_lean_saved_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
        "errors": errors, "checks": checks, "execution": identity(result_path),
        "comparison": identity(receipt_path), "proof_review": identity(PACKET / "quality/CALENDAR-FIXTURE-PROOF-REVIEW.json"),
        "preserved_output_files": 30, "current_pins_checked": len(receipt["pins_after"]),
        "cases": 3, "ordered_views": 38, "terms": 66, "adversarial_controls": 8,
        "reviewer": identity(Path(__file__)),
        "scope": "Actual three bounded imported original Lean completed-literal-word evaluations and whole coefficient/witness checks. Saved Rust comparison is separate. No solver is rerun here. Specific finite calendar phase/physical instances, universal parser/encoder refinement and scientific source admission are not inferred.",
        "source_admission_verified": False, "master_complete": False,
    }
    (PACKET / "quality/CALENDAR-LEAN-EXECUTION-REVIEW.json").write_text(
        json.dumps(answer, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors,
                      "preserved_output_files": 30, "current_pins_checked": answer["current_pins_checked"]}))
    return not answer["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
