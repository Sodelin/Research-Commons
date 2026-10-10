#!/usr/bin/env python3
"""Bounded native affine component, fresh receipts and independent checking.

CLI: --request PATH --output NEWDIR --binary PATH
     [--expected-binary-sha256 SHA]

The component reports MATRIX_WITNESS/MATRIX_EXCLUSION only for the supplied
rational affine matrix. SOURCE_ADMISSION_NOT_ESTABLISHED remains explicit.
It stages one read of the binary and request, preserves echoed RC1 bytes,
launches the native checker separately and also launches a pinned Fraction
checker. An observed digest is not a verified external binary pin or signature.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import time
from types import ModuleType

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
FRACTION_HELPER = HERE.parent / "design/certificate_check.py"
# Filled from the design owner's final helper, rather than accepting its hash
# from user input. It binds the staged helper bytes to a reviewed package file.
EXPECTED_FRACTION_HELPER_SHA = "ec55b12c10b8e5fd2eec29f72b4d14138b57d84139239e04e0c8907602e58e24"
CHART_FRACTION_HELPER = HERE.parent / "design/chart_check.py"
EXPECTED_CHART_FRACTION_HELPER_SHA = "3de5f13954f6aa40b53c0cf5a8b57d8895046becfd36989087fb6ec0748b5e8a"
SCHEMA = "rust_affine_component_result_v1"
CHART_SCHEMA = "rust_natural_cell_component_result_v1"
MAX_REQUEST_BYTES = 65536
MAX_CERTIFICATE_BYTES = 4 * 1024 * 1024
MAX_BINARY_BYTES = 128 * 1024 * 1024
HEX = re.compile(r"[0-9a-f]{64}\Z")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_regular(path, limit):
    path = Path(path).absolute()
    if path.is_symlink() or not path.is_file():
        raise ValueError("Regular nonsymlink file required: " + str(path))
    with path.open("rb") as handle:
        data = handle.read(limit + 1)
    if len(data) > limit:
        raise ValueError("Input byte limit exceeded: " + str(path))
    return path, data


def child_limits():
    os.setsid()
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))
    resource.setrlimit(resource.RLIMIT_AS, (512 * 1024 * 1024, 512 * 1024 * 1024))
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 1024 * 1024, 16 * 1024 * 1024))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def run_child(command, output, name, input_bytes=None):
    receipt = {"schema": "native_affine_execution_v1", "command": list(map(str, command)),
               "process_started": False, "exit_code": None, "timed_out": False,
               "cpu_limit_seconds": 30, "wall_timeout_seconds": 45,
               "address_space_bytes": 512 * 1024 * 1024,
               "per_file_bytes": 16 * 1024 * 1024,
               "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    before = time.monotonic()
    stdout = output / (name + ".stdout")
    stderr = output / (name + ".stderr")
    minimal_env = {"PATH": os.defpath, "LANG": "C.UTF-8", "PYTHONDONTWRITEBYTECODE": "1",
                   "PYTHONNOUSERSITE": "1", "PYTHONHASHSEED": "0"}
    with stdout.open("xb") as out, stderr.open("xb") as err:
        try:
            process = subprocess.Popen(list(map(str, command)), stdin=subprocess.PIPE,
                                       stdout=out, stderr=err, env=minimal_env,
                                       cwd=output, preexec_fn=child_limits)
            receipt["process_started"] = True
            try:
                process.communicate(input=input_bytes, timeout=45)
            except subprocess.TimeoutExpired:
                receipt["timed_out"] = True
                os.killpg(process.pid, signal.SIGKILL)
                process.communicate()
            receipt["exit_code"] = process.returncode
        except OSError as error:
            receipt.update(error_type=type(error).__name__, error=str(error))
    receipt.update(wall_seconds=time.monotonic() - before,
                   ended_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                   stdout_sha256=sha(stdout.read_bytes()), stderr_sha256=sha(stderr.read_bytes()),
                   stdout_bytes=stdout.stat().st_size, stderr_bytes=stderr.stat().st_size)
    (output / (name + ".execution.json")).write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return receipt


def capture_fraction_helper(operation="AFFINE"):
    base_bytes = None
    if operation == "CHART":
        base_bytes, base_module = capture_fraction_helper("AFFINE")
        # The reviewed CHART checker imports this module. Supply the captured
        # pinned module directly instead of importing another mutable path.
        sys.modules["certificate_check"] = base_module
    path, expected = ((FRACTION_HELPER, EXPECTED_FRACTION_HELPER_SHA) if operation == "AFFINE"
                      else (CHART_FRACTION_HELPER, EXPECTED_CHART_FRACTION_HELPER_SHA))
    data = path.read_bytes()
    if sha(data) != expected:
        raise ValueError("Pinned Fraction certificate checker identity mismatch")
    module = ModuleType("native_pinned_fraction_checker_" + operation.lower())
    module.__file__ = str(path)
    sys.modules[module.__name__] = module
    exec(compile(data, str(path), "exec"), module.__dict__)
    if operation == "CHART":
        # One self-contained staged entry executes both pinned captured byte
        # buffers. Python -I can stay enabled: no companion path imports occur.
        staged = ("import sys, types\n"
                  "base = types.ModuleType('certificate_check')\n"
                  "sys.modules['certificate_check'] = base\n"
                  f"exec(compile({base_bytes!r}, 'pinned_certificate_check.py', 'exec'), base.__dict__)\n"
                  "chart = types.ModuleType('__main__')\n"
                  "chart.__file__ = __file__\n"
                  "sys.modules['__main__'] = chart\n"
                  f"exec(compile({data!r}, 'pinned_chart_check.py', 'exec'), chart.__dict__)\n").encode("utf-8")
        return staged, module
    return data, module


def source_identities(operation="AFFINE"):
    manifest = json.loads((HERE / "INHERITED-SOURCES.json").read_text())
    for entry in manifest["files"]:
        path = ROOT / entry["path"]
        data = path.read_bytes()
        if sha(data) != entry["sha256"]:
            raise ValueError("Inherited source identity mismatch: " + entry["path"])
    identities = {"inherited": manifest,
            "owned_observed": [{"path": str(path.relative_to(ROOT)), "sha256": sha(path.read_bytes())}
                               for path in sorted(HERE.glob("src/*.rs"))],
            "fraction_checker_sha256": (EXPECTED_FRACTION_HELPER_SHA if operation == "AFFINE"
                                        else EXPECTED_CHART_FRACTION_HELPER_SHA),
            "claim": "Inherited pins and staged Fraction helper checked; owned hashes observed. "
                     "This does not prove arbitrary supplied binary was built from these sources."}
    if operation == "CHART":
        identities["fraction_checker_sources"] = [
            {"path": str(FRACTION_HELPER.relative_to(ROOT)), "sha256": EXPECTED_FRACTION_HELPER_SHA},
            {"path": str(CHART_FRACTION_HELPER.relative_to(ROOT)), "sha256": EXPECTED_CHART_FRACTION_HELPER_SHA},
        ]
    return identities


def execute(request, output, binary, expected_binary_sha256=None, *, operation="AFFINE"):
    if operation not in ("AFFINE", "CHART"):
        raise ValueError("Unsupported native component operation")
    output = Path(output).absolute()
    output.mkdir(parents=True, exist_ok=False)
    component = output / "component"
    component.mkdir()
    native = component / "native"
    native.mkdir()
    result = {"schema": SCHEMA if operation == "AFFINE" else CHART_SCHEMA,
              "operation": operation, "execution_mode": "FRESH_COMPONENT_EXECUTION",
              "status": "REFUSED_REQUEST", "solver_called": False, "checker_called": False,
              "fraction_checker_called": False, "source_admission": "SOURCE_ADMISSION_NOT_ESTABLISHED",
              "source_admission_verified": False,
              "scope": "One supplied finite rational affine matrix, all rows on one shared vector. "
                       "No typed graph/chart admission, source existence, whole-source registry "
                       "coverage, statistical confidence, biological accuracy or unrestricted G3/G4 decision.",
              "source_witness_certified": False, "unrestricted_exclusion_certified": False,
              "complete_source_registry_verified": False, "certificate_checked": False,
              "binary_expected_sha256": expected_binary_sha256,
              "binary_pin_verification": "NOT_REQUESTED_OBSERVED_HASH_ONLY",
              "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    exit_code = 1
    try:
        if expected_binary_sha256 is not None and not HEX.fullmatch(expected_binary_sha256):
            raise ValueError("Expected binary SHA256 must be 64 lowercase hexadecimal characters")
        request_path, raw = read_regular(request, MAX_REQUEST_BYTES)
        result.update(request_path=str(request_path), request_sha256=sha(raw))
        (output / "REQUEST.rc1").write_bytes(raw)
        helper_bytes, helper = capture_fraction_helper(operation)
        parsed = helper.parse_request(raw)
        if parsed[0] != operation:
            raise ValueError("This component requires RC1 " + operation)
        if operation == "CHART":
            result["fraction_checker_staged_sha256"] = sha(helper_bytes)
            result["scope"] = ("Literal original-ID natural cell, software-validated rooted binary structural predicates, "
                               "exact forms compiled jointly on one shared age/inverse-rate/coin bank. "
                               "Typed-source refinement, active-epoch chart coverage, cut-child/class admission, "
                               "observation-law fitting, statistical confidence and unrestricted G3/G4 remain unestablished.")
        (output / "SOURCE-IDENTITIES.json").write_text(json.dumps(source_identities(operation), indent=2, sort_keys=True) + "\n")
        binary_path, binary_bytes = read_regular(binary, MAX_BINARY_BYTES)
        digest = sha(binary_bytes)
        result.update(binary_path=str(binary_path), binary_observed_sha256=digest,
                      supplied_binary_source_build_verified=False)
        if expected_binary_sha256 is not None:
            if digest != expected_binary_sha256:
                result["binary_pin_verification"] = "MISMATCH_REFUSED_BEFORE_LAUNCH"
                raise ValueError("Supplied binary does not match expected SHA256")
            result["binary_pin_verification"] = "EXPECTED_PIN_MATCHED"
        staged_binary = native / "parity-solver"
        staged_binary.write_bytes(binary_bytes)
        staged_binary.chmod(0o700)
        staged_helper = native / "certificate_check.py"
        staged_helper.write_bytes(helper_bytes)
        producer = run_child([staged_binary], component, "solver", raw)
        result["solver_called"] = producer["process_started"]
        result["solver_execution"] = producer
        if not producer["process_started"] or producer["timed_out"] or producer["exit_code"] not in (0, 2):
            result["status"] = "RESOURCE_OR_EXECUTION_FAILURE"
        else:
            certificate = (component / "solver.stdout").read_bytes()
            if len(certificate) > MAX_CERTIFICATE_BYTES:
                raise ValueError("Certificate exceeds checker byte limit")
            (output / "CERTIFICATE.rc1").write_bytes(certificate)
            result["certificate_sha256"] = sha(certificate)
            # Authenticate the complete echo before choosing a checker branch.
            # SAT/UNSAT arithmetic runs in a separately bounded Fraction child.
            prefix = ("RC1 RESULT " + operation + "\nBEGIN_REQUEST\n").encode("ascii") + raw + b"END_REQUEST\n"
            if not certificate.startswith(prefix):
                raise ValueError("Certificate changed or omitted the request identity")
            remainder = certificate[len(prefix):]
            if operation == "CHART":
                marker = b"END_MATRIX\nGATE SOURCE_ADMISSION_NOT_ESTABLISHED\n"
                if marker not in remainder:
                    raise ValueError("Chart certificate omits matrix or mandatory source gate")
                remainder = remainder.split(marker, 1)[1]
            body = remainder.split(b"\n", 1)[0]
            matrix_status = {b"STATUS SAT": "SAT", b"STATUS UNSAT": "UNSAT",
                             b"STATUS UNKNOWN": "UNKNOWN"}.get(body)
            result["matrix_status"] = matrix_status
            expected_exit = {"SAT": 0, "UNSAT": 0, "UNKNOWN": 2}.get(matrix_status)
            if expected_exit is None or producer["exit_code"] != expected_exit:
                raise ValueError("Producer status and exit code violate the RC1 contract")
            if matrix_status == "UNKNOWN":
                helper.check_response(raw, certificate, producer["exit_code"])
                result.update(status="UNKNOWN", unknown_reason=operation + "_PROJECTION_CAP_EXHAUSTED",
                              certificate_checked=False)
                exit_code = 2
            elif matrix_status in ("SAT", "UNSAT"):
                checker = run_child([staged_binary, "check", output / "REQUEST.rc1", output / "CERTIFICATE.rc1"],
                                    component, "checker")
                result["checker_called"] = checker["process_started"]
                result["checker_execution"] = checker
                fraction = run_child([sys.executable, "-I", "-B", staged_helper, "--request", output / "REQUEST.rc1",
                                      "--certificate", output / "CERTIFICATE.rc1", "--exit-code", str(producer["exit_code"])],
                                     component, "fraction-checker")
                result["fraction_checker_called"] = fraction["process_started"]
                result["fraction_checker_execution"] = fraction
                accepted = (checker["process_started"] and checker["exit_code"] == 0 and not checker["timed_out"]
                            and (component / "checker.stdout").read_bytes() == b"RC1 CHECK ACCEPT\n"
                            and fraction["process_started"] and fraction["exit_code"] == 0 and not fraction["timed_out"])
                if accepted:
                    result.update(status="MATRIX_WITNESS" if matrix_status == "SAT" else "MATRIX_EXCLUSION",
                                  certificate_checked=True)
                    exit_code = 0
                else:
                    if (not checker["process_started"] or checker["timed_out"]
                            or not fraction["process_started"] or fraction["timed_out"]):
                        result["status"] = "RESOURCE_OR_EXECUTION_FAILURE"
                    else:
                        result.update(status="RESOURCE_OR_EXECUTION_FAILURE", failure_reason="CERTIFICATE_REJECTED")
            else:
                raise ValueError("Unexpected matrix component status")
    except (ValueError, OSError, UnicodeError, KeyError, OverflowError) as error:
        result.update(error_type=type(error).__name__, error=str(error))
        if result["solver_called"]:
            result.update(status="RESOURCE_OR_EXECUTION_FAILURE", failure_reason="INVALID_PRODUCER_OUTPUT")
    finally:
        result["exit_code"] = exit_code
        result["ended_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        (output / "RESULT.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        report = (f"# Native {operation.lower()} matrix result\n\nStatus: **{result['status']}**.\n\n"
                  f"Source admission: **{result['source_admission']}**.\n\n{result['scope']}\n\n"
                  f"Producer started: {result['solver_called']}; native checker started: {result['checker_called']}; "
                  f"Fraction checker started: {result['fraction_checker_called']}.\n\n"
                  f"Binary identity: {result['binary_pin_verification']}. Digests detect byte changes; they are not signatures.\n")
        (output / "REPORT.md").write_text(report)
        paths = sorted(path for path in output.rglob("*") if path.is_file())
        manifest = [{"path": str(path.relative_to(output)), "bytes": path.stat().st_size,
                     "sha256": sha(path.read_bytes())} for path in paths]
        (output / "ARTIFACTS.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--expected-binary-sha256")
    args = parser.parse_args()
    try:
        result = execute(args.request, args.output, args.binary, args.expected_binary_sha256)
    except (ValueError, OSError) as error:
        print(json.dumps({"schema": SCHEMA, "status": "REFUSED_REQUEST", "error": str(error),
                          "solver_called": False, "checker_called": False}))
        raise SystemExit(1)
    print(json.dumps({"schema": SCHEMA, "status": result["status"], "output": str(args.output.absolute()),
                      "source_admission": result["source_admission"]}))
    raise SystemExit(result["exit_code"])


if __name__ == "__main__":
    main()
