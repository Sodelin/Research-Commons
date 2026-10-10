#!/usr/bin/env python3
"""Recheck preserved original boundary output and scoped kernel evidence.

No compiler, evaluator or native producer is launched. The reference enumerates
whole-Copy bit assignments independently of the current-owner native compiler.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import time

import boundary_oracle as oracle

DESIGN = Path(__file__).resolve().parent
LEAN = DESIGN.parent / "lean"
SOURCE = DESIGN / "evidence/boundary-lean-rust-review-1"


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
        oracle.require(wanted is None or actual == wanted, "preserved boundary pin differs: " + str(path))
        observed[str(path)] = actual
        return path.read_bytes()

    certificate = oracle.parse_json(bind(LEAN / "ORIGINAL-BOUNDARY-FIXTURE-CERTIFICATE.json"))
    result = oracle.parse_json(bind(LEAN / "ORIGINAL-BOUNDARY-NATIVE-EXECUTION-RESULT.json"))
    receipt = oracle.parse_json(bind(SOURCE / "RECEIPT.json", result["coefficient_review_receipt_sha256"]))
    oracle.require(result["status"] == "PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL" and
                   result["fixtures_total"] == result["fixtures_passed"] == 12 and
                   result["all_actual_imported_artifacts_compiler_and_native_libraries_final_stable"],
                   "original evaluator qualification is incomplete")
    oracle.require(receipt["pass"] and receipt["cases_passed"] == receipt["cases_total"] == 12 and
                   receipt["execution_modes"]["lean"] == "compiled_lean_evaluator_not_standalone_elf" and
                   not receipt["Lean_standalone_ELF_claim"], "original boundary execution scope differs")
    prep = oracle.parse_json(bind(LEAN / "ORIGINAL-BOUNDARY-NATIVE-EXECUTION-PREPARATION.json",
                                 result["configuration_sha256"]))
    bind(Path(prep["compiler_path"]), prep["compiler_sha256"])
    bind(Path(prep["driver_path"]), prep["driver_sha256"])
    for item in prep["additional_native_provider_boundary"]:
        bind(Path(item), "4a6766a336deb036d13de56c73a50b6af073252a743cf6587e7f401f9312419e")
    bind(DESIGN / "evidence/epoch-native-closure-review-2/RECEIPT.json",
         "da7848e1aedae26fec050be5d5c8adadfa0fa9d9fdd9dc0678fe552c8efdc595")

    evidence = LEAN / certificate["evidence"]
    manifest = oracle.parse_json(bind(evidence / "PRESERVATION-MANIFEST.json",
                                     certificate["preservation_manifest_sha256"]))
    oracle.require(manifest["status"] == "PASS_ALL_REQUESTED_TARGETS" and
                   not manifest["original_attempts_overwritten"], "kernel preservation status differs")
    for entry in manifest["preserved_files"]:
        bind(evidence / entry["path"], entry["sha256"])
    graph = oracle.parse_json(bind(evidence / "DEPENDENCY-GRAPH.json", certificate["graph_sha256"]))
    sources, audits = {}, []
    for target, details in certificate["targets"].items():
        oracle.require(details["status"] == "PASS_FRESH_AGGREGATE_AND_COMPLETE_OWNED_AUDIT" and
                       not details["owned_axioms"] and not details["nonstandard_axiom_rows"] and
                       not details["missing_modules"] and details["source_and_import_bindings_stable"],
                       "boundary kernel target scope differs")
        raw = gzip.decompress((evidence / details["audit_distribution"]).read_bytes())
        oracle.require(hashlib.sha256(raw).hexdigest() == details["audit_raw_sha256"],
                       "decoded original boundary audit differs")
        audits.append({"target": target, "modules": details["closure_modules"],
                       "declarations": details["owned_declarations"], "theorems": details["owned_theorems"],
                       "decoded_audit_sha256": details["audit_raw_sha256"]})
        for name, record in graph["targets"][target]["modules"].items():
            path = Path(certificate["workspace"]) / "source-store" / (record["sha256"] + ".lean")
            bind(path, record["sha256"])
            oracle.require(certificate["source_pins"][name] == record["sha256"],
                           "boundary source graph is not the certified graph")
            sources[name] = record["sha256"]
    for item in certificate["derivatives"]:
        bind(Path(item["source"]), item["source_sha256"])

    for name in ["review_saved_boundary.py", "boundary_oracle.py", "epoch_oracle.py", "population_oracle.py"]:
        path = DESIGN / name
        bind(path)
        (args.output / name).write_bytes(path.read_bytes())
    expected_all, cases = {}, []
    for name, fixture in oracle.fixtures().items():
        expected, literal, unranked = oracle.expected_probe(name, *fixture)
        expected_all[name] = expected
        oracle.require(oracle.exact_json(oracle.parse_json(bind(SOURCE / (name + ".expected.json")))) ==
                       oracle.exact_json(expected), "saved boundary expectation differs")
        case = next(row for row in receipt["cases"] if row["fixture"] == name)
        for language in ["lean", "rust"]:
            run = case["runs"][language]
            oracle.require(run["process_started"] and run["exit_code"] == 0 and not run["timed_out"],
                           "saved boundary process status differs")
            output = bind(SOURCE / (name + "." + language + ".stdout"), run["stdout_sha256"])
            bind(SOURCE / (name + "." + language + ".stderr"), run["stderr_sha256"])
            oracle.check_probe(oracle.parse_json(output), expected, literal, unranked)
        cases.append({"fixture": name, "selected_views": len(expected["rows"]),
                      "literal_states": len(literal), "both_saved_outputs": "PASS"})
    controls = oracle.asymmetric_controls(expected_all)
    after = {path: digest(Path(path)) for path in observed}
    oracle.require(observed == after, "saved boundary evidence changed during review")
    answer = {"schema": "saved_original_boundary_independent_review_v1", "status": "PASS",
              "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
              "new_compiler_or_producer_execution": False, "cases_total": len(cases),
              "selected_views_total": sum(row["selected_views"] for row in cases),
              "original_source_versions_rechecked": len(sources), "separate_audits": audits,
              "native_closure_qualification": "Reuses separately audited unchanged 670-module generated-C closure; rechecks the loaded library identity.",
              "full_import_artifact_resweep": False,
              "controls": controls, "cases": cases, "pins_before": observed, "pins_after": after,
              "general_native_refinement_proved": False, "source_admission_verified": False,
              "standalone_Lean_ELF_claimed": False}
    (args.output / "RECEIPT.json").write_text(json.dumps(answer, indent=2) + "\n")
    print("PASS", len(cases), answer["selected_views_total"], flush=True)


if __name__ == "__main__":
    main()
