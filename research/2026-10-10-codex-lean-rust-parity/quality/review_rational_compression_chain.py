#!/usr/bin/env python3
"""Bind accepted native, typed, kernel and execution reviews without reruns."""
import json
from datetime import datetime, timezone
from pathlib import Path
from review_support_join import PACKET, identity, read


def main():
    names = ["RATIONAL-COMPRESSION-NATIVE-REVIEW.json",
             "RATIONAL-COMPRESSION-PROOF-REVIEW.json",
             "RATIONAL-COMPRESSION-LITERAL-REVIEW.json",
             "RATIONAL-COMPRESSION-FIXTURE-PROOF-REVIEW.json",
             "RATIONAL-COMPRESSION-EXECUTION-REVIEW.json",
             "RATIONAL-COMPRESSION-FACTS-REVIEW.json"]
    reviews = {name: read(PACKET / "quality" / name) for name in names}
    independent_path = PACKET / "rust/evidence/rational-compression-lean-rust-review-4/RECEIPT.json"
    independent = read(independent_path)
    errors = [name for name, row in reviews.items() if not row["pass"] or row["errors"]]
    for path, digest in independent["inputs_after"].items():
        if identity(Path(path))["sha256"] != digest:
            errors.append("Independent current input: " + path)
    checks = {
        "exact_independent_receipt": identity(independent_path)["sha256"]
            == "cb98230132db5fd0ac9816a49d2222394c0f4bcb1c3a9207f9e48507a04315b0",
        "independent_saved_native_and_lean_agreement": independent["pass"]
            and independent["native_certificates_rechecked"] == 8
            and independent["typed_certificate_cases"] == 6
            and independent["actual_lean_check_count"] == 9
            and independent["wrong_tail_controls"] == 3
            and independent["inputs_before"] == independent["inputs_after"]
            and independent["new_native_processes"] == independent["new_lean_processes"] == 0,
        "whole_imported_execution_context_checked": reviews["RATIONAL-COMPRESSION-EXECUTION-REVIEW.json"]["current_artifact_pins_checked"]
            == 25744 and reviews["RATIONAL-COMPRESSION-EXECUTION-REVIEW.json"]["checks_total"] == 9,
        "separate_kernel_ground_facts": reviews["RATIONAL-COMPRESSION-FACTS-REVIEW.json"]["proof"]["targets"][0]["counts"]
            == [100, 2691, 1680],
        "source_and_general_native_gates_remain_open": not independent["source_admission_verified"]
            and not independent["source_factor_realization_verified"]
            and not independent["arbitrary_real_extraction_verified"]
            and not independent["native_json_or_producer_refinement_proved"],
    }
    errors.extend(k for k, v in checks.items() if not v)
    answer = {"schema": "rational_compression_supplied_certificate_chain_root_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
        "errors": errors, "checks": checks,
        "root_reviews": {n: identity(PACKET / "quality" / n) for n in names},
        "independent_saved_comparison": identity(independent_path),
        "reviewer": identity(Path(__file__)),
        "scope": "The private bounded M2..4 Rust port reuses the old exact rational elimination. Saved Rust output is bound to typed original-index Lean literals, actual compiled checker outcomes, a generic checker-to-original-population compression theorem and a separate kernel theorem for the closed finite outcomes. Module/case/row counts overlap and are not added. This establishes the declared supplied-certificate chain, not a proof of every native parser/elimination run or biological source realization.",
        "new_native_processes": 0, "new_lean_processes": 0,
        "general_native_refinement_proved": False, "source_reconstruction_complete": False,
        "master_complete": False}
    (PACKET / "quality/RATIONAL-COMPRESSION-CHAIN-REVIEW.json").write_text(
        json.dumps(answer, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors, "root_reviews": len(names)}))
    return not answer["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
