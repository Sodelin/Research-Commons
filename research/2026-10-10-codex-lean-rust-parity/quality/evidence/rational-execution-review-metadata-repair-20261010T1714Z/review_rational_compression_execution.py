#!/usr/bin/env python3
"""Check saved compiled Lean outcomes and their exact imported context."""
import json
from datetime import datetime, timezone
from pathlib import Path
from review_support_join import PACKET, identity, read


def main():
    result_path = PACKET / "lean/RATIONAL-COMPRESSION-FIXTURE-EVALUATOR-RESULT.json"
    result = read(result_path)
    evidence = PACKET / "lean" / result["evidence"]
    receipt = read(evidence / "RECEIPT.json")
    config = read(evidence / "LEAN-EXECUTION-CONFIG.json")
    process = read(evidence / "LEAN-PROCESS-RESULT.json")
    preservation = read(evidence / "PRESERVATION-MANIFEST.json")
    bindings = read(evidence / "SOURCE-INPUT-BINDINGS.json")
    pins = read(evidence / "PRE-EVALUATION-PINS.json")
    certificate_path = PACKET / "lean/RATIONAL-COMPRESSION-FIXTURE-CERTIFICATE.json"
    certificate = read(certificate_path)
    reviews = {name: read(PACKET / "quality" / name) for name in (
        "RATIONAL-COMPRESSION-FIXTURE-PROOF-REVIEW.json",
        "RATIONAL-COMPRESSION-LITERAL-REVIEW.json",
        "RATIONAL-COMPRESSION-PROOF-REVIEW.json",
        "RATIONAL-COMPRESSION-NATIVE-REVIEW.json")}
    errors = []
    for row in preservation["files"]:
        if identity(evidence / row["path"]) != {k: row[k] for k in ("bytes", "sha256")}:
            errors.append("Preserved output: " + row["path"])
    for path, digest in pins.items():
        if identity(Path(path))["sha256"] != digest:
            errors.append("Imported/current artifact: " + path)
    for row in bindings["origins"]:
        original = PACKET / row["path"]
        if identity(original)["sha256"] != row["sha256"]:
            errors.append("Saved origin: " + row["path"])
        if row["path"].startswith("rust/"):
            if identity(evidence / "saved-origin" / row["path"])["sha256"] != row["sha256"]:
                errors.append("Copied origin: " + row["path"])
    expected = [(name, name != "sameMassWrongTail") for name in (
        "historicalM2", "historicalM3", "historicalM4", "empty", "allZero",
        "sameMassWrongTail", "wrongTailMass", "wrongTailOtherPremises", "wrongTailMomentDiffers")]
    expected_stdout = "".join(f"{name}: {str(value).lower()} (expected {str(value).lower()})\n"
                              for name, value in expected)
    reference = read(evidence / "REFERENCE-RESULTS.json")
    kernel_evidence = PACKET / "lean" / config["kernel_evidence"]
    checks = {
        "four_independent_reviews_pass": all(r["pass"] and not r["errors"] for r in reviews.values()),
        "complete_exact_preservation": len(preservation["files"]) == 30
            and identity(evidence / "PRESERVATION-MANIFEST.json")["sha256"] == result["preservation_manifest_sha256"]
            and not preservation["original_kernel_and_native_artifacts_modified"],
        "receipt_and_config_bound": identity(evidence / "RECEIPT.json")["sha256"] == result["receipt_sha256"]
            and identity(evidence / "LEAN-EXECUTION-CONFIG.json")["sha256"]
            == result["execution_config_sha256"] == receipt["execution_config_sha256"],
        "actual_bounded_checked_process": process["exit_code"] == 0
            and 0 < process["seconds"] < process["timeout_seconds"] == 60
            and process["command"] == config["command_prefix"]
            and process["command"][0] == config["compiler_path"]
            and all(arg in process["command"] for arg in ("-j1", "-t0", "-M4096", "-Ddebug.skipKernelTC=false", "--run"))
            and config["execution_mode"] == receipt["execution_mode"] == "compiled_lean_evaluator_not_standalone_elf",
        "exact_compiler_and_driver": identity(Path(config["compiler_path"]))["sha256"]
            == config["compiler_sha256"] == receipt["compiler_sha256"]
            and identity(Path(config["driver_path"]))["sha256"] == config["driver_sha256"]
            and Path(config["driver_path"]).read_text() == "import G6RationalCompressionCertificateFixtureMain\n\n",
        "actual_stdout_and_stderr": (evidence / "lean.stdout").read_text() == expected_stdout
            and not (evidence / "lean.stderr").read_bytes()
            and all(identity(evidence / ("lean." + suffix))["sha256"] == process[suffix + "_sha256"]
                    for suffix in ("stdout", "stderr")),
        "all_nine_finite_outcomes": receipt["cases"] == [{"name": n, "actual": v} for n, v in expected]
            and config["fixtures"] == [n for n, _ in expected]
            and receipt["checks"] == 9 and receipt["certificate_cases"] == 6
            and receipt["extra_wrong_tail_controls"] == 3
            and [(r["name"], r["expected"]) for r in reference] == expected[:6]
            and all(r["mass_preserved"] and r["other_premises"] for r in reference)
            and reference[-1]["input_tail_moments"] != reference[-1]["output_tail_moments"],
        "typed_literal_capture_bound": bindings["finite_literal_table_values_match_saved_requests_and_results"]
            and bindings["capture_sha256"] == receipt["capture_sha256"]
            == identity(evidence / "FINITE-INPUT-CAPTURE.json")["sha256"]
            == identity(PACKET / "reuse/RATIONAL-COMPRESSION-EXAMPLES-CAPTURE-20261010T165956Z.json")["sha256"],
        "complete_kernel_context_bound": identity(certificate_path)["sha256"] == result["kernel_certificate_sha256"]
            == reviews["RATIONAL-COMPRESSION-FIXTURE-PROOF-REVIEW.json"]["proof"]["certificate"]["sha256"]
            and certificate["evidence"] == receipt["kernel_evidence"] == config["kernel_evidence"]
            and config["source_pins"] == certificate["source_pins"]
            and (config["closure_modules"], config["owned_declarations"], config["owned_theorems"]) == (100, 2691, 1678)
            and not config["owned_axioms"] and not config["nonstandard_axiom_rows"]
            and identity(PACKET / "lean/RATIONAL-COMPRESSION-FIXTURE-CDDC-RESULT.json")["sha256"] == config["kernel_result_sha256"]
            and identity(kernel_evidence / "PRESERVATION-MANIFEST.json")["sha256"] == config["kernel_preservation_manifest_sha256"],
        "exact_imported_artifact_context": config["actual_imported_artifact_count"] == 25688
            and not config["additional_native_provider_boundary"]
            and len(pins) == 25744 and receipt["all_pre_post_artifact_identities_stable"],
        "only_saved_native_inputs": receipt["private_native_binary_sha256"]
            == "f5822d80fdc9a68d967edf95406f9d9a3cc4f6bb56b104418a19ee69e72671d8"
            and result["native_producer_processes"] == receipt["native_producer_processes"] == 0
            and result["lean_evaluator_processes"] == receipt["lean_evaluator_processes"] == 1
            and not receipt["old_native_tests_reexecuted"],
        "no_universal_or_source_claim": not receipt["universal_native_parser_or_elimination_refinement_claimed"]
            and not receipt["source_positive_factor_or_arbitrary_real_extraction_claimed"],
    }
    errors.extend(key for key, value in checks.items() if not value)
    answer = {"schema": "rational_compression_actual_lean_saved_root_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
        "errors": errors, "checks": checks, "execution": identity(result_path),
        "receipt": identity(evidence / "RECEIPT.json"), "preserved_files": 30,
        "current_artifact_pins_checked": len(pins), "certificate_cases": 6, "checks_total": 9,
        "reviewer": identity(Path(__file__)),
        "scope": "One actual compiled imported Lean evaluator agrees with saved typed Rust certificate data: five valid cases, one false moment forgery and three true premise controls. Root rehashes the entire saved imported context and does not run Lean or Rust. Computational truth here is separate from the pending kernel Facts theorem; no universal native refinement or source reconstruction follows.",
        "kernel_ground_facts_inferred": False, "general_native_refinement_inferred": False,
        "source_admission_verified": False, "master_complete": False}
    (PACKET / "quality/RATIONAL-COMPRESSION-EXECUTION-REVIEW.json").write_text(
        json.dumps(answer, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors, "pins": len(pins), "checks": 9}))
    return not answer["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
