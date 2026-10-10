#!/usr/bin/env python3
"""Four sole-scheduler-only application/reference composition controls.

No build or unchanged broad suite. Use a fresh /dev/shm output directory;
preserve text receipts without copying staged ELF executables to the repo.
This source was authored/syntax checked without starting any target process.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
APP = ROOT / "applications/practical-solver/run.py"
APP_SHA = "e21c8099de6f82137f7fff046d0738d878a196a50b65bd0eaa9a73441ac4a916"
ADAPTER = HERE / "native_source_fit_component.py"
ADAPTER_SHA = "0a895c793714e3e5f38b0d9f6ae6dbc9464c5bd0dd14700677e05a9091dbde18"
BINARY_SHA = "443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00"
COMMON = HERE / "fixtures/source-fit/hybrid-common-sat.request.json"
COMMON_SHA = "63d6b2242c428d98fe89c3c6e6295948026de220095a3fe852d5e66069db6591"
FOUR = HERE.parent / "design/fixtures/source-fit-reference-four-copy-fork.request.json"
FOUR_SHA = "b5e8cede35e35568e01a085f058574332fd16d59da32e780511f657f9a4e5341"
SCIENCE_FALSE = ("certificate_valid", "source_admission_verified", "source_observation_fit_verified",
    "source_provenance_verified", "timed_readout_verified", "full_code_evaluated",
    "universal_native_refinement_verified", "full_solver_verified", "source_witness_certified",
    "unrestricted_exclusion_certified", "complete_source_registry_verified",
    "observation_law_admission_verified", "statistical_confidence_verified",
    "physical_survival_image_verified", "full_joint_calendar_law_verified")
APP_FALSE = ("statistical_coverage_verified", "parameter_accuracy_released",
    "whole_application_lean_verified", "original_nine_parameter_producer_called")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def save(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--reference-python", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.absolute()
    out.mkdir(parents=True, exist_ok=False)
    tests = []
    receipt = {"schema": "source_fit_application_reference_runtime_review_v1", "status": "FAILED",
        "compiler_processes_started": 0, "source_admission_verified": False,
        "universal_native_refinement_verified": False, "full_solver_verified": False,
        "scope": "Four fresh launcher controls: selected-reference COMMON/four-copy, missing-reference failure, native-only default."}
    try:
        for path, expected in ((APP,APP_SHA),(ADAPTER,ADAPTER_SHA),(args.binary,BINARY_SHA),
                               (COMMON,COMMON_SHA),(FOUR,FOUR_SHA)):
            require(sha(path.read_bytes()) == expected, "frozen input/source changed: " + str(path))
        cases = (("common-reference", COMMON, True, False, 3),
                 ("four-copy-reference", FOUR, True, False, 15),
                 ("missing-reference", COMMON, True, True, 0),
                 ("native-only-default", COMMON, False, False, 3))
        for name, origin, selected, missing, rows in cases:
            case = out/name
            case.mkdir()
            raw = origin.read_bytes()
            request = case/"REQUEST.json"
            request.write_bytes(raw)
            application = case/"application"
            command = [sys.executable,"-B",str(APP),"source-fit-readout","--request",str(request),
                "--output",str(application),"--native-binary",str(args.binary.absolute()),
                "--expected-binary-sha256",BINARY_SHA]
            if selected:
                reference = out/"absent-reference-python" if missing else args.reference_python.absolute()
                command.extend(("--reference-python",str(reference)))
            started = time.monotonic()
            with (case/"stdout").open("xb") as stdout, (case/"stderr").open("xb") as stderr:
                process = subprocess.run(command, stdout=stdout, stderr=stderr, timeout=200, check=False)
            app_bytes = (application/"RESULT.json").read_bytes()
            child_bytes = (application/"component/RESULT.json").read_bytes()
            app, child = json.loads(app_bytes), json.loads(child_bytes)
            require(app["schema"] == "practical_solver_component_result_v1"
                and child["schema"] == "rust_source_fit_component_result_v1", name+": wrong result schema")
            require(app["component"] == "source-fit-readout" and child["operation"] == "READOUT", name+": wrong operation")
            require(app["component_result"] == child, name+": embedded child differs from exact saved result")
            require(app["launcher_sha256"] == APP_SHA and app["component_source_sha256"] == ADAPTER_SHA
                and app["component_source_unchanged"] is True, name+": source binding missing")
            require(app["request_bytes_sha256"] == child["request_sha256"] == sha(raw), name+": raw request hash changed")
            require((application/"REQUEST.json").read_bytes() == raw
                and (application/"component/REQUEST.json").read_bytes() == raw, name+": request snapshots changed")
            require(all(app.get(flag) is False and child.get(flag) is False for flag in SCIENCE_FALSE), name+": scientific claim promoted")
            require(all(app.get(flag) is False for flag in APP_FALSE), name+": full application claim promoted")
            require(child["reference_requested"] is selected, name+": selected reference option changed")
            for outer, inner in (("native_solver_called","solver_called"),("native_checker_called","checker_called"),
                ("reference_checker_called","reference_checker_called"),
                ("independent_all_coefficients_checked","independent_all_coefficients_checked"),
                ("independent_probabilities_checked","independent_probabilities_checked")):
                require(type(app[outer]) is bool and app[outer] is child[inner], name+": start/verification flags changed")
            if missing:
                require(process.returncode == child["exit_code"] == 1 and app["status"] == child["status"] == "RESOURCE_OR_EXECUTION_FAILURE", name+": selected reference did not fail closed")
                require(not app["native_solver_called"] and not app["native_checker_called"] and not app["reference_checker_called"], name+": missing interpreter started children")
                require(not app["independent_all_coefficients_checked"] and not app["independent_probabilities_checked"], name+": missing reference promoted verification")
                require(not (application/"component/NATIVE-RESULT.json").exists(), name+": unexpected producer result")
            else:
                require(process.returncode == child["exit_code"] == 0 and app["status"] == child["status"] == "SUPPLIED_FIT_ROOTED_LAW", name+": successful TABLE omitted")
                for flag in ("component_called","native_solver_called","native_checker_called","native_replay_verified","supplied_trace_checked","rooted_law_evaluated"):
                    require(app.get(flag) is True, name+": checked execution missing "+flag)
                native_bytes = (application/"component/NATIVE-RESULT.json").read_bytes()
                require(child["native_result_sha256"] == sha(native_bytes), name+": native result digest changed")
                native = json.loads(native_bytes)
                require(native["bank_result"]["request"]["context"] == json.loads(raw)["context"], name+": original occurrence/copy registry changed")
                require(len(native["mixture"]) == rows and sum((Fraction(row["probability"]) for row in native["mixture"]), Fraction(0)) == 1, name+": full rooted rows/mass changed")
                if origin == COMMON:
                    expected = json.loads((HERE/"evidence/source-fit-program-reference-1/hybrid-common-sat.expected.json").read_bytes())
                    require(native["mixture"] == expected["rows"], name+": common full coefficients/probabilities changed")
                if selected:
                    for flag in ("reference_checker_called","independent_all_coefficients_checked","independent_probabilities_checked"):
                        require(app.get(flag) is True, name+": selected reference success guard omitted "+flag)
                    require(child["reference_identity_recheck_stable"] is True
                        and child["reference_baseline_called"] is True, name+": checked reference identity/backend missing")
                    checked = child["reference_check"]
                    require(checked["request_sha256"] == sha(raw) and checked["response_sha256"] == sha(native_bytes)
                        and checked["rooted_outcomes"] == rows, name+": complete reference/raw result binding changed")
                    checker_stdout = application/"component/component/reference-checker.stdout"
                    require(child["reference_result_sha256"] == sha(checker_stdout.read_bytes())
                        == child["reference_checker_execution"]["stdout_sha256"], name+": independent result digest missing")
                else:
                    require(not app["reference_checker_called"] and not app["independent_all_coefficients_checked"]
                        and not app["independent_probabilities_checked"] and not child["reference_baseline_called"], name+": native-only default promoted reference")
                    require(not (application/"component/component/REFERENCE-RUNTIME.json").exists(), name+": native-only invoked reference backend")
            item = {"name":name,"pass":True,"command":command,"exit_code":process.returncode,
                "wall_seconds":time.monotonic()-started,"status":app["status"],"selected_reference":selected,
                "request_sha256":sha(raw),"application_result_sha256":sha(app_bytes),"child_result_sha256":sha(child_bytes),
                "stdout_sha256":sha((case/"stdout").read_bytes()),"stderr_sha256":sha((case/"stderr").read_bytes()),
                "rooted_outcomes":rows}
            save(case/"RECEIPT.json",item)
            tests.append(item)
        require(sha(APP.read_bytes()) == APP_SHA and sha(ADAPTER.read_bytes()) == ADAPTER_SHA,
            "watched launcher/adapter changed during batch")
        require(sha(args.binary.read_bytes()) == BINARY_SHA, "native binary changed during batch")
        receipt.update(status="PASS",checks=4,launcher_sha256=APP_SHA,adapter_sha256=ADAPTER_SHA,binary_sha256=BINARY_SHA)
    except (ValueError,OSError,KeyError,TypeError,subprocess.TimeoutExpired) as error:
        receipt.update(error_type=type(error).__name__,error=str(error))
    finally:
        receipt["tests"]=tests
        save(out/"RECEIPT.json",receipt)
    print(json.dumps({"status":receipt["status"],"output":str(out)},sort_keys=True))
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
