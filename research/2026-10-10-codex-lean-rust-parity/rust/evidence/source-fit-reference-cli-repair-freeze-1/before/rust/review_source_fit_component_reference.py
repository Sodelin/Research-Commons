#!/usr/bin/env python3
"""Sole-scheduler-only optional reference component controls.

Run in a fresh /dev/shm output directory: this stages native executables.
The owner authored/syntax-checked this harness without launching targets.
No compiler or unchanged broad suite is called. Preserve text receipts and
hashes without copying staged ELF binaries into distributed evidence.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ADAPTER = HERE / "native_source_fit_component.py"
ADAPTER_SHA = "69634f3a8e0fbbdb4b96b852557f18776d51fa8df4427e78cf3d664894dcf1bb"
BINARY_SHA = "443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00"
HELPER = HERE.parent / "design/source_fit_reference.py"
HELPER_SHA = "0eedff2d9ab21514e3788ae5f9310e33bd57d8ce86e4cf038bb08520ccd99fc6"
CASES = (
    ("hybrid-common-sat", "63d6b2242c428d98fe89c3c6e6295948026de220095a3fe852d5e66069db6591"),
    ("hybrid-independent-sat", "0d3d30b9be0cf8ccbb9473c5fdeffd6a4c6a129fa122fff1ea0b181411dd7ef4"),
    ("hybrid-common-permuted", "a01f07c1cd2fa5a84880bd46ea7a3890356af9c936ca4873ebd5bb7b5f40875e"),
)
SAVED_COMMON = HERE / "evidence/source-fit-native-slot-20261010T221453.635194Z/cli-challenges/hybrid-common-sat-readout-file/stdout"
SAVED_COMMON_SHA = "3f21282fe0bdc8ecba4e8d4b4779ce3dfc3677bf4bccf904ff367c760b966039"
FOUR_COPY_SHA = "b5e8cede35e35568e01a085f058574332fd16d59da32e780511f657f9a4e5341"
FALSE_FLAGS = ("certificate_valid", "source_admission_verified", "source_observation_fit_verified",
    "source_provenance_verified", "timed_readout_verified", "full_code_evaluated",
    "universal_native_refinement_verified", "full_solver_verified", "source_witness_certified",
    "unrestricted_exclusion_certified", "complete_source_registry_verified",
    "observation_law_admission_verified", "statistical_confidence_verified",
    "physical_survival_image_verified", "full_joint_calendar_law_verified",
    "provider_work_checked", "provider_exhaustion_verified")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def wire(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def add_term(row, power, delta):
    terms = {tuple(p): Fraction(q) for p, q in row["edge_polynomial"]}
    key = tuple(power)
    terms[key] = terms.get(key, Fraction(0)) + delta
    if not terms[key]:
        del terms[key]
    row["edge_polynomial"] = [[list(p), f"{q.numerator}/{q.denominator}"] for p, q in sorted(terms.items())]


def execute_case(out, name, request, binary, reference_python, binary_sha):
    case = out / name
    case.mkdir()
    request_path = case / "REQUEST.json"
    request_path.write_bytes(request)
    component = case / "component"
    command = [sys.executable, "-B", str(ADAPTER), "--operation", "readout", "--request", str(request_path),
        "--output", str(component), "--binary", str(binary), "--expected-binary-sha256", binary_sha,
        "--reference-python", str(reference_python)]
    started = time.monotonic()
    with (case / "stdout").open("xb") as stdout, (case / "stderr").open("xb") as stderr:
        process = subprocess.run(command, stdout=stdout, stderr=stderr, timeout=200, check=False)
    receipt = {"command": command, "exit_code": process.returncode, "wall_seconds": time.monotonic()-started,
        "stdout_sha256": sha((case/"stdout").read_bytes()), "stderr_sha256": sha((case/"stderr").read_bytes()),
        "request_sha256": sha(request)}
    result = json.loads((component/"RESULT.json").read_bytes())
    require(result["request_sha256"] == sha(request), name + ": raw request not bound")
    require(result["exit_code"] == process.returncode, name + ": wrapper exit mismatch")
    require(all(result.get(flag) is False for flag in FALSE_FLAGS), name + ": scientific/work promotion")
    require(result["reference_requested"] is True, name + ": reference option omitted")
    receipt.update(status=result["status"], result_sha256=sha((component/"RESULT.json").read_bytes()),
        solver_called=result["solver_called"], checker_called=result["checker_called"],
        reference_checker_called=result["reference_checker_called"])
    (case/"RECEIPT.json").write_bytes(wire(receipt))
    return result, component, receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--reference-python", type=Path, required=True)
    parser.add_argument("--four-copy-request", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.absolute()
    out.mkdir(parents=True, exist_ok=False)
    results = []
    receipt = {"schema": "source_fit_component_reference_runtime_review_v1", "status": "FAILED",
        "compiler_processes_started": 0, "tests": [], "source_admission_verified": False,
        "universal_native_refinement_verified": False, "full_solver_verified": False,
        "scope": "Fresh optional-reference process composition; independent old full rooted coefficients/probabilities and fail-closed controls."}
    try:
        require(sha(ADAPTER.read_bytes()) == ADAPTER_SHA, "adapter source freeze changed")
        require(sha(HELPER.read_bytes()) == HELPER_SHA, "reference source freeze changed")
        require(sha(args.binary.read_bytes()) == BINARY_SHA, "private native binary identity changed")
        origins = {}
        for name, digest in CASES:
            raw = (HERE/"fixtures/source-fit"/(name+".request.json")).read_bytes()
            require(sha(raw) == digest, "fixture input changed: "+name)
            origins[name] = raw
            result, component, item = execute_case(out, name, raw, args.binary.absolute(), args.reference_python.absolute(), BINARY_SHA)
            require(result["status"] == "SUPPLIED_FIT_ROOTED_LAW" and result["exit_code"] == 0, name+": no checked TABLE")
            for flag in ("solver_called", "checker_called", "reference_checker_called", "native_replay_verified",
                         "independent_all_coefficients_checked", "independent_probabilities_checked",
                         "supplied_trace_arithmetic_checked", "reference_baseline_called", "reference_identity_recheck_stable"):
                require(result.get(flag) is True, name+": missing "+flag)
            checked = result["reference_check"]
            require(checked["rooted_outcomes"] == 3, name+": full row coverage changed")
            require(checked["response_sha256"] == sha((component/"NATIVE-RESULT.json").read_bytes()), name+": result digest changed")
            require(result["reference_result_sha256"] == result["reference_checker_execution"]["stdout_sha256"], name+": process output digest mismatch")
            table = json.loads((component/"NATIVE-RESULT.json").read_bytes())
            expected = json.loads((HERE/"evidence/source-fit-program-reference-1"/(name+".expected.json")).read_bytes())
            require(table["mixture"] == expected["rows"], name+": saved all-coefficient reference mismatch")
            require(result["reference_runtime_observed"]["backend_called"] is True, name+": backend use omitted")
            item.update(pass_=True, rooted_outcomes=3, whole_edge_terms=checked["whole_edge_terms"])
            results.append(item)

        if args.four_copy_request is not None:
            four = args.four_copy_request.read_bytes()
            require(sha(four) == FOUR_COPY_SHA, "four-copy input-only freeze changed")
            result, component, item = execute_case(out, "four-copy-fork", four, args.binary.absolute(), args.reference_python.absolute(), BINARY_SHA)
            require(result["status"] == "SUPPLIED_FIT_ROOTED_LAW" and result["exit_code"] == 0, "four-copy reference did not accept TABLE")
            for flag in ("reference_checker_called", "independent_all_coefficients_checked", "independent_probabilities_checked", "supplied_trace_arithmetic_checked"):
                require(result.get(flag) is True, "four-copy independent check omitted "+flag)
            checked = result["reference_check"]
            require(checked["rooted_outcomes"] == 15, "four-copy complete rooted row count changed")
            item.update(pass_=True, rooted_outcomes=15, whole_edge_terms=checked["whole_edge_terms"])
            results.append(item)

        raw = origins["hybrid-common-sat"]
        result, component, item = execute_case(out, "missing-reference", raw, args.binary.absolute(), out/"absent-python", BINARY_SHA)
        require(result["status"] == "RESOURCE_OR_EXECUTION_FAILURE" and result["exit_code"] == 1, "missing reference did not fail closed")
        require(not result["solver_called"] and not result["checker_called"] and not result["reference_checker_called"], "missing interpreter launched children")
        require(not result["independent_all_coefficients_checked"] and not result["independent_probabilities_checked"], "missing reference promoted flags")
        item.update(pass_=True); results.append(item)

        failed_python = out/"rejecting-reference-python"
        failed_python.write_text("#!/bin/sh\nexit 1\n")
        failed_python.chmod(0o700)
        result, component, item = execute_case(out, "failed-reference", raw, args.binary.absolute(), failed_python, BINARY_SHA)
        require(result["status"] == "RESOURCE_OR_EXECUTION_FAILURE" and result["exit_code"] == 1, "failed reference fell back to success")
        require(all(result[k] for k in ("solver_called", "checker_called", "reference_checker_called")), "postlaunch failure lost start provenance")
        require(result["checker_execution"]["exit_code"] == 0, "native replay was not accepted before reference failure")
        require(result["reference_result_sha256"] == result["reference_checker_execution"]["stdout_sha256"], "failure output digest omitted")
        require(not result["independent_all_coefficients_checked"] and not result["independent_probabilities_checked"], "failed reference promoted flags")
        item.update(pass_=True); results.append(item)

        unknown = json.loads(raw)
        unknown["limits"]["equations"] = 0
        result, component, item = execute_case(out, "frame-only-unknown", wire(unknown), args.binary.absolute(), args.reference_python.absolute(), BINARY_SHA)
        require(result["status"] == "UNKNOWN" and result["exit_code"] == 2, "native UNKNOWN changed")
        require(result["reference_checker_called"] and result["reference_frame_checked"], "UNKNOWN frame checker did not start/accept")
        require(not result["reference_baseline_called"] and not result["independent_all_coefficients_checked"] and not result["independent_probabilities_checked"], "UNKNOWN promoted table checks")
        require(result["reference_runtime_observed"]["backend_called"] is False and result["reference_runtime_observed"]["packages"] == {}, "frame-only UNKNOWN eagerly loaded backend")
        item.update(pass_=True); results.append(item)

        saved = SAVED_COMMON.read_bytes()
        require(sha(saved) == SAVED_COMMON_SHA, "original saved native TABLE changed")
        forged = json.loads(saved)
        n = len(forged["bank_result"]["request"]["context"]["edges"])
        zero, x0 = [0]*n, [1]+[0]*(n-1)
        value = Fraction(json.loads(raw)["values"][0]["value"])
        # Add +/- (x0-fitted_x0)/7 across two rows: mass and every fitted
        # probability stay unchanged, while the complete E coefficient law differs.
        for row, sign in zip(forged["mixture"][:2], (1,-1)):
            add_term(row, x0, Fraction(sign,7))
            add_term(row, zero, -Fraction(sign,7)*value)
        forged["configurations"][0]["outcomes"] = copy.deepcopy(forged["mixture"])
        require([r["probability"] for r in forged["mixture"]] == [r["probability"] for r in json.loads(saved)["mixture"]], "forgery changed fitted probabilities")
        fake = out/"forged-source-fit-solver"
        reply = wire(forged)
        fake.write_text(f"#!{Path(sys.executable).resolve()}\nimport sys\n"
            "if sys.argv[1] in ('check','check-readout'):\n"
            "    sys.stdout.buffer.write(b'{\"schema\":\"source_fit_check_v1\",\"status\":\"ACCEPT\"}\\n')\n"
            "elif sys.argv[1] == 'readout':\n"
            f"    sys.stdout.buffer.write({reply!r})\n"
            "else:\n    sys.exit(1)\n")
        fake.chmod(0o700)
        result, component, item = execute_case(out, "balanced-source-coefficient-forgery", raw, fake, args.reference_python.absolute(), sha(fake.read_bytes()))
        require(result["status"] == "RESOURCE_OR_EXECUTION_FAILURE" and result["exit_code"] == 1, "balanced coefficient forgery was promoted")
        require(all(result[k] for k in ("solver_called", "checker_called", "reference_checker_called")), "forgery lost actual starts")
        require(result["checker_execution"]["exit_code"] == 0, "fake native replay did not ACCEPT")
        failure = json.loads((component/"component/reference-checker.stdout").read_bytes())
        require(failure["result_valid"] is False and "full rooted whole-edge coefficient table differs" in failure["error"], "forgery failed for another reason")
        require(not result["independent_all_coefficients_checked"] and not result["independent_probabilities_checked"], "forgery promoted independent flags")
        item.update(pass_=True); results.append(item)

        require(sha(ADAPTER.read_bytes()) == ADAPTER_SHA and sha(HELPER.read_bytes()) == HELPER_SHA, "watched source changed during batch")
        require(sha(args.binary.read_bytes()) == BINARY_SHA, "native binary changed during batch")
        receipt.update(status="PASS", checks=len(results), rooted_outcomes=sum(r.get("rooted_outcomes",0) for r in results), whole_edge_terms=sum(r.get("whole_edge_terms",0) for r in results),
            adapter_sha256=ADAPTER_SHA, helper_sha256=HELPER_SHA, binary_sha256=BINARY_SHA)
    except (ValueError, OSError, KeyError, TypeError, subprocess.TimeoutExpired) as error:
        receipt.update(error_type=type(error).__name__, error=str(error))
    finally:
        receipt["tests"] = results
        (out/"RECEIPT.json").write_bytes(wire(receipt))
    print(json.dumps({"status":receipt["status"],"output":str(out)},sort_keys=True))
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
