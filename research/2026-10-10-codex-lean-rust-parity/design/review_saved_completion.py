#!/usr/bin/env python3
"""Independently recheck preserved original completion executions and evidence.

No compiler, Lean evaluator or Rust producer is launched. Exact spectral rows
and closed-form weights are regenerated; the original source artifacts and
saved native outputs are authenticated separately.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import time

import review_completion_compiled_fixtures as oracle

DESIGN = Path(__file__).resolve().parent
LEAN = DESIGN.parent / "lean"
SOURCE = DESIGN / "evidence/completion-compiled-oracle-actual-1"
RESULT_SHA = "0480f249bdf91bdda05948613f281bbe97d0d3b4b99c0e4dce6dacc282b23325"
CERTIFICATE_SHA = "74bc60bd774c3e04320808d156efcaf1eb1fa6f12ea3e54366a2f0eccfc215c4"
ORACLE_SHA = "f87671690a634f9a7c12094828f7b5e5b39fc36ef9bf32f142098d08e35f2602"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    observed = {}

    def bind(path, wanted=None):
        path = path.resolve()
        actual = digest(path)
        oracle.ref.require(wanted is None or actual == wanted, "preserved completion pin differs: " + str(path))
        observed[str(path)] = actual
        return path.read_bytes()

    parse = oracle.ref.epoch.parse_json
    certificate = parse(bind(LEAN / "ORIGINAL-COMPLETION-FIXTURE-CERTIFICATE.json", CERTIFICATE_SHA))
    result = parse(bind(LEAN / "ORIGINAL-COMPLETION-NATIVE-EXECUTION-RESULT.json", RESULT_SHA))
    receipt = parse(bind(SOURCE / "RECEIPT.json", result["coefficient_review_receipt_sha256"]))
    oracle.ref.require(result["status"] == "PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL" and
                       result["fixtures_total"] == result["fixtures_passed"] == 6 and
                       result["full_view_rows_total"] == 257 and
                       result["all_actual_imported_artifacts_compiler_and_native_libraries_final_stable"] and
                       not result["standalone_elf_claimed"] and not result["scientific_provider_gates_promoted"],
                       "original completion evaluator qualification is incomplete")
    oracle.ref.require(receipt["pass"] and receipt["cases_passed"] == receipt["cases_total"] == 6 and
                       receipt["full_view_rows_total"] == 257 and
                       receipt["execution_modes"]["lean"] == "compiled_lean_evaluator_not_standalone_elf" and
                       set(receipt["languages_executed"]) == {"lean", "rust"} and
                       not receipt["Lean_standalone_ELF_claim"] and not receipt["general_native_refinement_claim"] and
                       not receipt["source_admission_verified"] and not receipt["chosen_epoch_table_identity_claim"],
                       "original completion execution scope differs")
    oracle.ref.require(receipt["pins_before"] == receipt["pins_after"], "execution pins changed")
    prep = parse(bind(LEAN / "ORIGINAL-COMPLETION-NATIVE-EXECUTION-PREPARATION.json",
                      result["configuration_sha256"]))
    bind(Path(prep["compiler_path"]), prep["compiler_sha256"])
    bind(Path(prep["driver_path"]), prep["driver_sha256"])
    for path in prep["additional_native_provider_boundary"]:
        bind(Path(path), "4a6766a336deb036d13de56c73a50b6af073252a743cf6587e7f401f9312419e")
    bind(DESIGN / "evidence/epoch-native-closure-review-2/RECEIPT.json",
         "da7848e1aedae26fec050be5d5c8adadfa0fa9d9fdd9dc0678fe552c8efdc595")
    bind(LEAN / "scripts/run_completion_fixture_review.py", result["scheduler_sha256"])

    evidence = LEAN / certificate["evidence"]
    manifest = parse(bind(evidence / "PRESERVATION-MANIFEST.json", certificate["preservation_manifest_sha256"]))
    oracle.ref.require(manifest["status"] == "PASS_ALL_REQUESTED_TARGETS" and
                       not manifest["original_attempts_overwritten"], "completion kernel preservation differs")
    for entry in manifest["preserved_files"]:
        bind(evidence / entry["path"], entry["sha256"])
    graph = parse(bind(evidence / "DEPENDENCY-GRAPH.json", certificate["graph_sha256"]))
    sources, audits = {}, []
    for target, details in certificate["targets"].items():
        oracle.ref.require(details["status"] == "PASS_FRESH_AGGREGATE_AND_COMPLETE_OWNED_AUDIT" and
                           not details["owned_axioms"] and not details["nonstandard_axiom_rows"] and
                           not details["missing_modules"] and details["source_and_import_bindings_stable"],
                           "completion kernel target scope differs")
        raw = gzip.decompress((evidence / details["audit_distribution"]).read_bytes())
        oracle.ref.require(hashlib.sha256(raw).hexdigest() == details["audit_raw_sha256"],
                           "decoded completion audit differs")
        audit = json.loads(raw)
        oracle.ref.require(len(audit["selected_modules"]) == details["closure_modules"] and
                           audit["declaration_count"] == details["owned_declarations"] and
                           audit["theorem_declaration_count"] == details["owned_theorems"] and
                           not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and
                           not audit["missing_modules"], "decoded audit scope/counts differ")
        audits.append({"target": target, "modules": details["closure_modules"],
                       "declarations": details["owned_declarations"], "theorems": details["owned_theorems"],
                       "decoded_audit_sha256": details["audit_raw_sha256"]})
        for name, record in graph["targets"][target]["modules"].items():
            path = Path(certificate["workspace"]) / "source-store" / (record["sha256"] + ".lean")
            bind(path, record["sha256"])
            oracle.ref.require(certificate["source_pins"][name] == record["sha256"],
                               "completion source graph is not certified")
            sources[name] = record["sha256"]
    for item in certificate["derivatives"]:
        bind(Path(item["source"]), item["source_sha256"])

    bind(DESIGN / "review_completion_compiled_fixtures.py", ORACLE_SHA)
    for path, wanted in receipt["pins_before"].items():
        bind(Path(path), wanted)
    for name in ["review_saved_completion.py", "review_completion_compiled_fixtures.py",
                 "review_completion_controls.py", "source_word_oracle.py", "boundary_oracle.py",
                 "epoch_oracle.py", "population_oracle.py"]:
        path = DESIGN / name
        bind(path)
        (args.output / name).write_bytes(path.read_bytes())
    cases = []
    oracle.ref.require({row["fixture"] for row in receipt["cases"]} == set(oracle.NAMES),
                       "original completion fixture inventory differs")
    for name in oracle.NAMES:
        expected, word, internal, form = oracle.direct_expected(name)
        oracle.ref.require(oracle.ref.epoch.exact_json(parse(bind(SOURCE / (name + ".expected.json")))) ==
                           oracle.ref.epoch.exact_json(expected), "saved completion expectation differs")
        case = next(row for row in receipt["cases"] if row["fixture"] == name)
        for language in ["lean", "rust"]:
            run = case["runs"][language]
            oracle.ref.require(run["process_started"] and run["exit_code"] == 0 and not run["timed_out"] and
                               run["coefficient_review"]["status"] == "PASS", "saved completion process status differs")
            actual = parse(bind(SOURCE / (name + "." + language + ".stdout"), run["stdout_sha256"]))
            bind(SOURCE / (name + "." + language + ".stderr"), run["stderr_sha256"])
            if language == "rust":
                oracle.ref.check_probe(actual, word, internal)
                actual = {"schema": expected["schema"], "fixture": name, "context": expected["context"],
                          "rows": [{"view": row["view"], "witness": row["witness"],
                                    "weight": row["coefficients"][0][1]} for row in actual["rows"]]}
            oracle.check_direct(actual, expected, internal)
        cases.append({"fixture": name, "full_view_rows": len(expected["rows"]),
                      "literal_support_states": len(internal["literal"]), "closed_form": form,
                      "both_saved_outputs": "PASS"})
    controls = oracle.checker_controls()
    oracle.ref.require(controls == receipt["invalid_table_controls_rejected"], "completion controls differ")
    after = {path: digest(Path(path)) for path in observed}
    oracle.ref.require(observed == after, "completion evidence changed during review")
    answer = {"schema": "saved_original_completion_independent_review_v1", "status": "PASS",
              "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
              "new_compiler_or_producer_execution": False, "cases_total": len(cases),
              "full_view_rows_total": sum(row["full_view_rows"] for row in cases),
              "original_source_versions_rechecked": len(sources), "separate_audits": audits,
              "preserved_kernel_artifacts_rechecked": len(manifest["preserved_files"]),
              "native_closure_qualification": "Reuses independently audited unchanged 670-module generated-C closure; rechecks loaded library identity.",
              "full_import_artifact_resweep": False,
              "controls_rejected": controls, "cases": cases, "pins_before": observed, "pins_after": after,
              "general_native_refinement_proved": False, "source_admission_verified": False,
              "standalone_Lean_ELF_claimed": False, "chosen_epoch_table_identity_claimed": False}
    (args.output / "RECEIPT.json").write_text(json.dumps(answer, indent=2) + "\n")
    print("PASS", len(cases), answer["full_view_rows_total"], len(controls), flush=True)


if __name__ == "__main__":
    main()
