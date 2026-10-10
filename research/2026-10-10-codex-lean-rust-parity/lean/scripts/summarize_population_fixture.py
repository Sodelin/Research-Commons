#!/usr/bin/env python3
"""Report kernel, actual evaluator and independent finite comparison separately."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--review", type=Path)
    args = parser.parse_args()
    prep_path = ROOT / "POPULATION-EXECUTION-PREPARATION.json"
    prep = json.loads(prep_path.read_bytes())
    execution_path = ROOT / "POPULATION-EXECUTION-RESULT.json"
    execution = json.loads(execution_path.read_bytes())
    assert execution["status"] == "PASS_EIGHT_IMPORTED_ORIGINAL_COEFFICIENT_EXECUTIONS"
    assert execution["source_and_import_artifacts_stable"]
    assert execution["kernel_evidence"] == prep["kernel_evidence"]
    assert execution["fixture_source_sha256"] == prep["fixture_source_sha256"]
    review = {"status": "NOT_INCLUDED"}
    if args.review:
        path = args.review.resolve()
        data = json.loads(path.read_bytes())
        assert data["pass"] and data["cases_total"] == data["cases_passed"] == 8
        assert data["claim"] == "FINITE_ORIGINAL_COMPILED_EVALUATOR_COEFFICIENT_REVIEW"
        assert data["execution_modes"]["lean"] == "compiled_lean_evaluator_not_standalone_elf"
        assert data["binary_pins_before"] == data["binary_pins_after"]
        assert data["observed_input_pins_before"] == data["observed_input_pins_after"]
        assert data["lean_import_path"] == prep["lean_path"]
        assert {r["fixture"] for r in data["cases"]} == set(prep["fixtures"])
        review = {"status": "PASS_EIGHT_LITERAL_AND_COMPLETE_FIBRE_COMPARISONS",
                  "receipt_path": str(path), "receipt_sha256": sha(path),
                  "oracle_algorithm": data["oracle_algorithm"],
                  "oracle_sha256": data["oracle_sha256"],
                  "binary_pins": data["binary_pins_before"],
                  "case_census": [{k: r[k] for k in ["fixture", "literal_rows", "unordered_rows"]}
                                  for r in data["cases"]]}
    certificate = {"status": "PASS_CHECKED_ORIGINAL_POPULATION_FIXTURE_AND_FINITE_DIFFERENTIAL_REVIEW"
                   if args.review else "PASS_CHECKED_ORIGINAL_POPULATION_FIXTURE_AND_EVALUATOR_EXECUTION",
                   "kernel": {"evidence": prep["kernel_evidence"],
                              "result_sha256": prep["kernel_result_sha256"],
                              "closure_modules": prep["closure_modules"],
                              "owned_declarations": prep["declarations"], "owned_theorems": prep["theorems"],
                              "owned_axioms": [], "nonstandard_axiom_rows": []},
                   "proof_sources": {"arbitrary_fuel_support": prep["support_source_sha256"],
                                     "canonical_encoding_image": prep["encoding_image_source_sha256"]},
                   "inherited_population_provider_sha256": prep["population_provider_source_sha256"],
                   "fixture_source_sha256": prep["fixture_source_sha256"],
                   "actual_execution": {"mode": execution["execution_mode"], "evidence": execution["evidence"],
                                        "receipt_sha256": sha(execution_path), "fixtures_executed": 8,
                                        "artifacts_before_after_stable": True},
                   "independent_review": review,
                   "standalone_lean_elf_claimed": False, "general_native_LAW_quotient_proved": False,
                   "general_Rust_refinement_proved": False, "source_observation_admission_gate_promoted": False,
                   "preparation_sha256": sha(prep_path),
                   "scope": "Original effective coefficient definition on eight type-safe source-valid encoded entering states. General arbitrary-fuel zero-support and encoded-image preservation are proved; finite quotient tests do not establish universal label/orientation lumpability or whole-frontier refinement."}
    save(ROOT / "POPULATION-FIXTURE-CERTIFICATE.json", certificate)
    evidence = ROOT / execution["evidence"]
    save(evidence / "ACCEPTANCE-SUMMARY.json", certificate)
    print(json.dumps({"status": certificate["status"], "kernel": certificate["kernel"],
                      "independent_review": review["status"]}))


if __name__ == "__main__":
    main()
