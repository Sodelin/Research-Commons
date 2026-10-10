#!/usr/bin/env python3
"""Recheck preserved nine original-word evaluator and native coefficient tables.

No Lean, Rust or compiler process is launched. The original request bytes and
all complete coefficient/view/witness outputs are replayed against the frozen
coupled-generator reference. Kernel contexts and concrete source identities are
authenticated separately; no generic native implementation proof is inferred.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import time

import review_word_compiled_fixtures as oracle

DESIGN = Path(__file__).resolve().parent
LEAN = DESIGN.parent / "lean"
SOURCE = DESIGN / "evidence/word-compiled-oracle-actual-1"
ORACLE_SHA = "f0763dadfe55ba1f6ba40e2f545637966082347226c1796eeffea8cf4e6691c8"
CERTIFICATE_SHA = "d72691a06c52f81c1a4bb997fea911bb92ec2135eea6a3b367b95c5525ae2f9e"
RESULT_SHA = "da4a6f3f819b720a4d018dee726bd59d6bb45325ce4fdd4c970e2ba58ee7f256"
RECEIPT_SHA = "f6560784264d4c68b61b8c0be381bb13c7881ebf84dd13d30b3360e307ae6770"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    observed = {}
    require, parse = oracle.ref.require, oracle.ref.epoch.parse_json

    def bind(path, wanted=None):
        path = path.resolve()
        actual = digest(path)
        require(wanted is None or actual == wanted, "saved original-word artifact differs: " + str(path))
        observed[str(path)] = actual
        return path.read_bytes()

    certificate = parse(bind(LEAN / "ORIGINAL-WORD-FIXTURE-CERTIFICATE.json", CERTIFICATE_SHA))
    result = parse(bind(LEAN / "ORIGINAL-WORD-NATIVE-EXECUTION-RESULT.json", RESULT_SHA))
    receipt = parse(bind(SOURCE / "RECEIPT.json", RECEIPT_SHA))
    require(result["status"] == "PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL" and
            result["fixtures_total"] == result["fixtures_passed"] == 9 and result["full_view_rows_total"] == 39 and
            result["coefficient_review_receipt_sha256"] == RECEIPT_SHA and
            result["all_actual_imported_artifacts_compiler_and_native_libraries_final_stable"] and
            not result["standalone_elf_claimed"] and not result["scientific_provider_gates_promoted"] and
            not result["general_Rust_refinement_claimed"], "original-word evaluator qualification differs")
    require(receipt["pass"] and receipt["cases_total"] == receipt["cases_passed"] == 9 and
            receipt["full_view_rows_total"] == 39 and set(receipt["languages_executed"]) == {"lean", "rust"} and
            receipt["execution_modes"]["lean"] == "compiled_lean_evaluator_not_standalone_elf" and
            receipt["pins_before"] == receipt["pins_after"] and not receipt["Lean_native_work_counters_inferred"] and
            not receipt["general_native_refinement_claim"] and not receipt["source_admission_verified"] and
            not receipt["ancestral_completion_claim"], "original-word differential scope differs")
    config = parse(bind(LEAN / "ORIGINAL-WORD-NATIVE-EXECUTION-PREPARATION.json", result["configuration_sha256"]))
    bind(Path(config["compiler_path"]), config["compiler_sha256"])
    bind(Path(config["driver_path"]), config["driver_sha256"])
    for path in config["additional_native_provider_boundary"]:
        bind(Path(path), "4a6766a336deb036d13de56c73a50b6af073252a743cf6587e7f401f9312419e")
    bind(DESIGN / "evidence/epoch-native-closure-review-2/RECEIPT.json",
         "da7848e1aedae26fec050be5d5c8adadfa0fa9d9fdd9dc0678fe552c8efdc595")
    bind(LEAN / "scripts/run_word_fixture_review.py", result["scheduler_sha256"])
    require(result["design_review_script_sha256"] == ORACLE_SHA, "evaluator wrapper used a different comparator")
    bind(DESIGN / "review_word_compiled_fixtures.py", ORACLE_SHA)

    evidence = LEAN / certificate["evidence"]
    manifest = parse(bind(evidence / "PRESERVATION-MANIFEST.json", certificate["preservation_manifest_sha256"]))
    require(manifest["status"] == "PASS_ALL_REQUESTED_TARGETS" and not manifest["original_attempts_overwritten"],
            "original-word kernel preservation differs")
    for entry in manifest["preserved_files"]:
        bind(evidence / entry["path"], entry["sha256"])
    graph = parse(bind(evidence / "DEPENDENCY-GRAPH.json", certificate["graph_sha256"]))
    sources, audits = {}, []
    for target, details in certificate["targets"].items():
        require(details["status"] == "PASS_FRESH_AGGREGATE_AND_COMPLETE_OWNED_AUDIT" and
                not details["owned_axioms"] and not details["nonstandard_axiom_rows"] and
                not details["missing_modules"] and details["source_and_import_bindings_stable"],
                "original-word kernel target qualification differs")
        raw = gzip.decompress((evidence / details["audit_distribution"]).read_bytes())
        require(hashlib.sha256(raw).hexdigest() == details["audit_raw_sha256"], "decoded original-word audit differs")
        audit = json.loads(raw)
        require(len(audit["selected_modules"]) == details["closure_modules"] and
                audit["declaration_count"] == details["owned_declarations"] and
                audit["theorem_declaration_count"] == details["owned_theorems"] and
                not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
                "decoded original-word audit scope/counts differ")
        audits.append({"target": target, "modules": details["closure_modules"],
                       "declarations": details["owned_declarations"], "theorems": details["owned_theorems"],
                       "decoded_audit_sha256": details["audit_raw_sha256"]})
        for name, record in graph["targets"][target]["modules"].items():
            path = Path(certificate["workspace"]) / "source-store" / (record["sha256"] + ".lean")
            bind(path, record["sha256"])
            require(certificate["source_pins"][name] == record["sha256"], "original-word source graph binding differs")
            sources[name] = record["sha256"]
    for item in certificate["derivatives"]:
        bind(Path(item["source"]), item["source_sha256"])
    # These concrete roots discharge the generic hstep premise. Their contexts
    # overlap; the records are retained separately rather than added together.
    proof_roots = []
    for name in ["EFFECTIVE-INITIALIZATION-CERTIFICATE.json", "SELECTED-EPOCH-UNIQUENESS-CERTIFICATE.json",
                 "SPARSE-WORD-COMPOSITION-CERTIFICATE.json", "EFFECTIVE-NODE-CERTIFICATE.json",
                 "EFFECTIVE-WORD-CERTIFICATE.json"]:
        proof = parse(bind(LEAN / name))
        for derivative in proof["derivatives"]:
            module = derivative["module"]
            require(certificate["source_pins"][module] == derivative["source_sha256"],
                    "original fixture imported a different proof-root version")
            bind(Path(derivative["source"]), derivative["source_sha256"])
        for target, details in proof["targets"].items():
            require(details["status"] == "PASS_FRESH_AGGREGATE_AND_COMPLETE_OWNED_AUDIT" and
                    not details["owned_axioms"] and not details["nonstandard_axiom_rows"] and
                    not details["missing_modules"] and details["source_and_import_bindings_stable"],
                    "word prerequisite context is not accepted")
            raw = gzip.decompress((LEAN / proof["evidence"] / details["audit_distribution"]).read_bytes())
            require(hashlib.sha256(raw).hexdigest() == details["audit_raw_sha256"],
                    "word prerequisite decoded audit differs")
            audit = json.loads(raw)
            require(audit["declaration_count"] == details["owned_declarations"] and
                    audit["theorem_declaration_count"] == details["owned_theorems"] and
                    not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
                    "word prerequisite audit qualification differs")
            proof_roots.append({"certificate": name, "target": target, "modules": details["closure_modules"],
                                "declarations": details["owned_declarations"], "theorems": details["owned_theorems"]})
    for path, wanted in receipt["pins_before"].items():
        bind(Path(path), wanted)
    require({row["fixture"] for row in receipt["cases"]} == set(oracle.NAMES),
            "actual original-word fixture inventory differs")
    cases = []
    for name in oracle.NAMES:
        bind(oracle.origin(name))
        expected, word, internal = oracle.direct_expected(name)
        require(parse(bind(SOURCE / (name + ".expected.json"))) == expected,
                "saved exact original-word expectation differs")
        case = next(row for row in receipt["cases"] if row["fixture"] == name)
        require(case["pass"] and not case["errors"], "saved original-word case failed")
        for language in ("lean", "rust"):
            run = case["runs"][language]
            require(run["process_started"] and run["exit_code"] == 0 and not run["timed_out"],
                    "saved original-word process did not pass")
            actual = parse(bind(SOURCE / (name + "." + language + ".stdout"), run["stdout_sha256"]))
            bind(SOURCE / (name + "." + language + ".stderr"), run["stderr_sha256"])
            if language == "rust":
                oracle.ref.check_probe(actual, word, internal)
                actual = oracle.project_native(actual)
            require(oracle.check_direct(actual, expected, internal) == run["coefficient_review"],
                    "saved original-word complete coefficient review differs")
        cases.append({"fixture": name, "full_view_rows": len(expected["rows"]),
                      "literal_support_states": len(internal["literal"]), "frozen_request_origin": "PASS",
                      "both_saved_complete_outputs": "PASS"})
    controls = oracle.checker_controls()
    require(controls == receipt["invalid_table_controls_rejected"] == result["invalid_table_controls_rejected"],
            "original-word forged coefficient/view controls differ")
    for name in ["review_saved_word.py", "review_word_compiled_fixtures.py", "source_word_oracle.py"]:
        bind(DESIGN / name)
        (args.output / name).write_bytes((DESIGN / name).read_bytes())
    after = {path: digest(Path(path)) for path in observed}
    require(observed == after, "original-word evidence changed during saved review")
    answer = {"schema": "saved_original_word_independent_review_v1", "status": "PASS",
              "new_compiler_or_producer_execution": False, "cases_total": 9, "full_view_rows_total": 39,
              "cases": cases, "controls_rejected": controls, "separate_fixture_audits": audits,
              "separate_overlapping_proof_root_contexts": proof_roots,
              "preserved_kernel_artifacts_rechecked": len(manifest["preserved_files"]),
              "original_source_versions_rechecked": len(sources), "pins_before": observed, "pins_after": after,
              "full_imported_artifact_resweep": False,
              "native_closure_qualification": "Reuses independently authenticated unchanged 670-module generated-C provider closure; exact loaded plugin identity rechecked.",
              "general_Rust_Lean_refinement_proved": False, "Lean_standalone_ELF_claimed": False,
              "Lean_native_work_counters_inferred": False, "source_admission_verified": False,
              "calendar_or_completion_refinement_claimed": False,
              "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (args.output / "RECEIPT.json").write_text(json.dumps(answer, indent=2) + "\n")
    print("PASS", 9, 39, len(controls), len(sources), len(manifest["preserved_files"]), flush=True)


if __name__ == "__main__":
    main()
