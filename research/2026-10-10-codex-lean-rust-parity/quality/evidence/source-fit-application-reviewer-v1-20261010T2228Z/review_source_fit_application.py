#!/usr/bin/env python3
"""Read saved application executions, bindings, scope flags and fixture laws."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

from review_preserved_run import review

PACKET = Path(__file__).resolve().parents[1]
FALSE = ("certificate_valid", "source_admission_verified", "source_observation_fit_verified",
         "source_provenance_verified", "timed_readout_verified", "full_code_evaluated",
         "universal_native_refinement_verified", "full_solver_verified",
         "physical_survival_image_verified", "statistical_confidence_verified")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    evidence = args.evidence.resolve()
    preservation = review(evidence / "PRESERVATION-MANIFEST.json")
    manifest = json.loads((evidence / "PRESERVATION-MANIFEST.json").read_bytes())
    final_raw = (evidence / "FINAL-RECEIPT.json").read_bytes()
    final = json.loads(final_raw)
    work = Path(final["workspace"])
    rows = []
    fixture_names = {"common-readout": "hybrid-common-sat", "independent-readout": "hybrid-independent-sat",
                     "permuted-readout": "hybrid-common-permuted"}
    for case in final["cases"]:
        name = case["name"]
        appdir = work / name / "application"
        appraw = (appdir / "RESULT.json").read_bytes()
        childraw = (appdir / "component/RESULT.json").read_bytes()
        app, child = json.loads(appraw), json.loads(childraw)
        if (sha(appraw) != case["application_result_sha256"]
                or sha(childraw) != case["component_result_sha256"]
                or child != app["component_result"]):
            raise ValueError("Application/component result identity: " + name)
        if (case["status"] != "PASS" or case["exit_code"] != case["expected_exit_code"]
                or app["status"] != child["status"] != case["expected_status"]):
            raise ValueError("Saved case status/exit mismatch: " + name)
        if app["status"] != case["expected_status"] or child["exit_code"] != case["exit_code"]:
            raise ValueError("Saved result status/exit mismatch: " + name)
        request_raw = (appdir / "REQUEST.json").read_bytes()
        if sha(request_raw) != app["request_bytes_sha256"] or sha(request_raw) != child["request_sha256"]:
            raise ValueError("Raw request binding: " + name)
        if not app["component_called"] or not app["execution"]["process_started"]:
            raise ValueError("Missing actual adapter start: " + name)
        if any(app.get(key) is not False or child.get(key) is not False for key in FALSE):
            raise ValueError("Unestablished scientific gate promoted: " + name)
        if (app["native_solver_called"] != child["solver_called"]
                or app["native_checker_called"] != child["checker_called"]):
            raise ValueError("Native start evidence differs: " + name)
        successful = app["status"] in ("SUPPLIED_FIT_BANK", "SUPPLIED_FIT_ROOTED_LAW")
        if successful and not all(child.get(key) is True for key in
                ("solver_called", "checker_called", "native_replay_verified", "supplied_trace_checked",
                 "semantic_request_echo_checked", "source_identity_recheck_stable", "staged_identity_recheck_stable")):
            raise ValueError("Missing bounded native success checks: " + name)
        selected_reference = "--reference-python" in case["command"]
        if successful and selected_reference:
            if not all(child.get(key) is True for key in ("reference_checker_called",
                    "independent_all_coefficients_checked", "independent_probabilities_checked")):
                raise ValueError("Requested independent reference absent: " + name)
        elif child["reference_checker_called"] or child["independent_all_coefficients_checked"]:
            raise ValueError("Native-only result promotes an unselected reference: " + name)
        if name == "mismatched-pin" and (child["solver_called"] or child["checker_called"]):
            raise ValueError("Wrong trusted digest reached native execution")
        if name in fixture_names and successful:
            fixture = json.loads((PACKET / "rust/fixtures/source-fit" / (fixture_names[name] + ".expected.json")).read_bytes())
            response = json.loads((appdir / "component/NATIVE-RESULT.json").read_bytes())
            actual = [{key: row[key] for key in ("tree", "probability")} for row in response["mixture"]]
            if actual != fixture["expected_global_rows"]:
                raise ValueError("Saved whole rooted law differs: " + name)
        rows.append({"name": name, "status": app["status"], "exit_code": case["exit_code"],
                     "application_sha256": sha(appraw), "component_sha256": sha(childraw),
                     "reference_selected": selected_reference, "request_sha256": sha(request_raw)})
    executables = manifest.get("staged_executables_preserved_at_fixed_scratch_paths", [])
    for row in executables:
        raw = Path(row["path"]).read_bytes()
        if sha(raw) != row["sha256"] or len(raw) != row["bytes"]:
            raise ValueError("Preserved staged executable identity mismatch")
    result = {"schema": "source_fit_application_saved_root_review_v1", "status": "PASS_SAVED_EXECUTION_BINDINGS_AND_SCOPE",
              "observed_utc": datetime.now(timezone.utc).isoformat(), "reviewer_sha256": sha(Path(__file__).read_bytes()),
              "final_receipt_sha256": sha(final_raw), "preservation": preservation, "cases": rows,
              "staged_executables_rehashed": len(executables), "compiler_or_law_provider_called": False,
              "source_admission_or_universal_refinement_inferred": False}
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": result["status"], "cases": len(rows),
                      "staged_executables_rehashed": len(executables)}))


if __name__ == "__main__":
    main()
