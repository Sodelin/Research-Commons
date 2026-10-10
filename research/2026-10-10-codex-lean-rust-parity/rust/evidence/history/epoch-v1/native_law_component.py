#!/usr/bin/env python3
"""Bounded formal genealogy-law component with independent source replay.

--request PATH --output NEWDIR --binary PATH [--expected-binary-sha256 SHA]

FORMAL_GENEALOGY_TABLE describes the complete formal supplied-source terminal
genealogy polynomial table. Natural physical-image/source/observation admission
and statistical/census conclusions remain false. The native check is disclosed
as forward replay; independent checking compares the attributed compiler.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time
from types import ModuleType

import native_component as transport

HERE = Path(__file__).resolve().parent
ROOT = transport.ROOT
SCHEMA = "rust_genealogy_law_component_result_v1"
EXPECTED_LAW_HELPER_SHA = "d6c62271373c2b4a6fd60aa1371d8d6a582368f4506e2d6bc2e3da43704b3e4d"
BASELINE_SHA = "eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7"
SYMPY_VERSION = "1.14.0"
MPMATH_VERSION = "1.3.0"


def capture_sources():
    specs = [
        ("certificate_check", HERE.parent / "design/certificate_check.py", transport.EXPECTED_FRACTION_HELPER_SHA),
        ("chart_check", HERE.parent / "design/chart_check.py", transport.EXPECTED_CHART_FRACTION_HELPER_SHA),
        ("pinned_law_checker", HERE.parent / "design/law_check.py", EXPECTED_LAW_HELPER_SHA),
        ("independent_pinned_inherited_law_compiler", ROOT / "research/2026-10-01-g7-continuous-design/law_compiler.py", BASELINE_SHA),
    ]
    buffers, identities = [], []
    checker = None
    for name, path, expected in specs:
        _, raw = transport.read_regular(path, 1024 * 1024)
        if transport.sha(raw) != expected:
            raise ValueError("Pinned LAW checker/provider source identity mismatch: " + str(path))
        identities.append({"module": name, "path": str(path.relative_to(ROOT)), "sha256": expected})
        buffers.append((name, raw))
        if name != "independent_pinned_inherited_law_compiler":
            module = ModuleType(name)
            module.__file__ = str(path)
            sys.modules[name] = module
            exec(compile(raw, str(path), "exec"), module.__dict__)
            if name == "pinned_law_checker":
                checker = module

    # Isolated child imports only its explicit installed scientific runtime.
    # Every source-dependent checker/provider import is supplied captured bytes.
    stage = ("import sys, types, json, hashlib\nfrom pathlib import Path\n"
             "import sympy, mpmath\n"
             "runtime = {}\n"
             "for package in (sympy, mpmath):\n"
             "    path = Path(package.__file__)\n"
             "    runtime[package.__name__] = {'version': package.__version__, 'origin': str(path), "
             "'initializer_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}\n"
             "runtime['claim'] = 'Observed package versions/origins/initializer identities; no entire third-party runtime verification.'\n"
             "Path('SYMPY-RUNTIME.json').write_text(json.dumps(runtime, indent=2, sort_keys=True)+'\\n')\n"
             f"if sympy.__version__ != {SYMPY_VERSION!r} or mpmath.__version__ != {MPMATH_VERSION!r}:\n"
             "    print(json.dumps({'result_valid': False, 'error': 'LAW scientific runtime version mismatch'}))\n"
             "    sys.exit(1)\n")
    # The inherited provider must be registered before the checker runs its
    # baseline_module(), preventing another mutable source-path read.
    ordered = [buffers[0], buffers[1], buffers[3], buffers[2]]
    for name, raw in ordered:
        stage += (f"module = types.ModuleType({name!r})\nmodule.__file__ = __file__\n"
                  f"sys.modules[{name!r}] = module\n"
                  f"exec(compile({raw!r}, {name!r}, 'exec'), module.__dict__)\n")
    stage += ("try:\n    sys.exit(module.main())\n"
              "except (ValueError, UnicodeError, OSError) as error:\n"
              "    print(json.dumps({'result_valid': False, 'error': str(error)}, sort_keys=True))\n"
              "    sys.exit(1)\n")
    return stage.encode("utf-8"), checker, identities


def execute(request, output, binary, expected_binary_sha256=None):
    output = Path(output).absolute()
    output.mkdir(parents=True, exist_ok=False)
    component = output / "component"
    component.mkdir()
    native = component / "native"
    native.mkdir()
    result = {
        "schema": SCHEMA, "operation": "LAW", "execution_mode": "FRESH_COMPONENT_EXECUTION",
        "status": "REFUSED_REQUEST", "solver_called": False, "checker_called": False,
        "fraction_checker_called": False, "reference_checker_called": False,
        "native_checker_mode": "REPLAY_FULL_JOINT_LAW",
        "native_checker_algorithm_independent": False,
        "source_admission": "SOURCE_ADMISSION_NOT_ESTABLISHED", "source_admission_verified": False,
        "source_witness_certified": False, "unrestricted_exclusion_certified": False,
        "physical_survival_image_verified": False, "observation_law_admission_verified": False,
        "full_joint_calendar_law_verified": False, "statistical_confidence_verified": False,
        "complete_source_registry_verified": False, "formal_table_checked": False,
        "certificate_checked": False,
        "inherited_baseline_all_coefficients_checked": False,
        "scope": "Complete formal supplied-source terminal rooted genealogy table and root-suppressed unrooted pushforward. "
                 "Natural physical survival image, typed/class/active-word admission, full joint calendar readout, "
                 "source census and statistical/biological conclusions remain unestablished.",
        "binary_expected_sha256": expected_binary_sha256,
        "binary_pin_verification": "NOT_REQUESTED_OBSERVED_HASH_ONLY",
        "scientific_runtime_requirements": {"sympy": SYMPY_VERSION, "mpmath": MPMATH_VERSION},
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    exit_code = 1
    try:
        if expected_binary_sha256 is not None and not transport.HEX.fullmatch(expected_binary_sha256):
            raise ValueError("Expected binary SHA256 must be 64 lowercase hexadecimal characters")
        request_path, raw = transport.read_regular(request, transport.MAX_REQUEST_BYTES)
        result.update(request_path=str(request_path), request_sha256=transport.sha(raw))
        (output / "REQUEST.rc1").write_bytes(raw)
        staged_checker, helper, source_pins = capture_sources()
        parsed = helper.parse_law(raw)
        identities = transport.source_identities()
        identities["law_checker_provider_sources"] = source_pins
        identities["staged_law_checker_sha256"] = transport.sha(staged_checker)
        result["staged_law_checker_sha256"] = transport.sha(staged_checker)
        (output / "SOURCE-IDENTITIES.json").write_text(json.dumps(identities, indent=2, sort_keys=True) + "\n")
        binary_path, binary_bytes = transport.read_regular(binary, transport.MAX_BINARY_BYTES)
        digest = transport.sha(binary_bytes)
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
        helper_path = native / "law_check.py"
        helper_path.write_bytes(staged_checker)
        producer = transport.run_child([staged_binary], component, "solver", raw)
        result.update(solver_called=producer["process_started"], solver_execution=producer)
        if not producer["process_started"] or producer["timed_out"] or producer["exit_code"] not in (0, 2):
            result["status"] = "RESOURCE_OR_EXECUTION_FAILURE"
        else:
            table_bytes = (component / "solver.stdout").read_bytes()
            if len(table_bytes) > transport.MAX_CERTIFICATE_BYTES:
                raise ValueError("LAW response exceeds checker byte limit")
            (output / "TABLE.rc1").write_bytes(table_bytes)
            result["table_sha256"] = transport.sha(table_bytes)
            prefix = b"RC1 RESULT LAW\nBEGIN_REQUEST\n" + raw + b"END_REQUEST\n"
            prefix += ("VARIABLES " + str(len(parsed.variables)) + " " + " ".join(parsed.variables)
                       + "\nGATE SOURCE_ADMISSION_NOT_ESTABLISHED\n").encode("ascii")
            if not table_bytes.startswith(prefix):
                raise ValueError("LAW response changed request, variable registry or source gate")
            status_line = table_bytes[len(prefix):].split(b"\n", 1)[0]
            law_status = {b"STATUS TABLE": "TABLE", b"STATUS UNKNOWN": "UNKNOWN"}.get(status_line)
            result["law_status"] = law_status
            if law_status is None or producer["exit_code"] != {"TABLE": 0, "UNKNOWN": 2}[law_status]:
                raise ValueError("LAW producer status and exit code violate the RC1 contract")
            if law_status == "UNKNOWN":
                checked = helper.verify_law_certificate(raw, table_bytes, producer["exit_code"])
                result.update(status="UNKNOWN", unknown_reason="LAW_" + checked["limit_kind"] + "_BUDGET",
                              unknown_metadata=checked, unknown_mathematical_exclusion=False)
                exit_code = 2
            else:
                checker = transport.run_child([staged_binary, "check", output / "REQUEST.rc1", output / "TABLE.rc1"],
                                              component, "checker")
                result.update(checker_called=checker["process_started"], checker_execution=checker)
                reference = transport.run_child([sys.executable, "-I", "-B", helper_path,
                    "--request", output / "REQUEST.rc1", "--certificate", output / "TABLE.rc1",
                    "--exit-code", str(producer["exit_code"])], component, "reference-checker")
                result.update(fraction_checker_called=reference["process_started"],
                              reference_checker_called=reference["process_started"], reference_checker_execution=reference)
                runtime_path = component / "SYMPY-RUNTIME.json"
                if runtime_path.is_file():
                    result["scientific_runtime_observed"] = json.loads(runtime_path.read_text())
                accepted = (checker["process_started"] and checker["exit_code"] == 0 and not checker["timed_out"]
                            and (component / "checker.stdout").read_bytes() == b"RC1 CHECK ACCEPT\n"
                            and reference["process_started"] and reference["exit_code"] == 0 and not reference["timed_out"])
                if accepted:
                    checked = json.loads((component / "reference-checker.stdout").read_text())
                    accepted = (checked.get("status") == "TABLE" and checked.get("result_valid") is True
                                and checked.get("inherited_baseline_all_coefficients_checked") is True
                                and checked.get("polynomial_normalization_checked") is True
                                and checked.get("unrooted_pushforward_checked") is True
                                and checked.get("source_admission_established") is False)
                if accepted:
                    result.update(status="FORMAL_GENEALOGY_TABLE", formal_table_checked=True,
                                  inherited_baseline_all_coefficients_checked=True, reference_check=checked)
                    exit_code = 0
                else:
                    result.update(status="RESOURCE_OR_EXECUTION_FAILURE", failure_reason="LAW_REPLAY_OR_BASELINE_REJECTED")
    except (ValueError, OSError, UnicodeError, KeyError, OverflowError) as error:
        result.update(error_type=type(error).__name__, error=str(error))
        if result["solver_called"]:
            result.update(status="RESOURCE_OR_EXECUTION_FAILURE", failure_reason="INVALID_PRODUCER_OUTPUT")
    finally:
        result.update(exit_code=exit_code, ended_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        (output / "RESULT.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        (output / "REPORT.md").write_text(
            f"# Formal genealogy-law result\n\nStatus: **{result['status']}**.\n\n"
            f"Source admission: **{result['source_admission']}**.\n\n{result['scope']}\n\n"
            f"Producer started: {result['solver_called']}; native replay started: {result['checker_called']}; "
            f"independent coefficient checker started: {result['reference_checker_called']}.\n\n"
            "SymPy/mpmath versions and origins are observed in the bounded checker process; "
            "their complete runtime has no universal verification claim.\n")
        files = sorted(path for path in output.rglob("*") if path.is_file())
        artifacts = [{"path": str(path.relative_to(output)), "bytes": path.stat().st_size,
                      "sha256": transport.sha(path.read_bytes())} for path in files]
        (output / "ARTIFACTS.json").write_text(json.dumps(artifacts, indent=2, sort_keys=True) + "\n")
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
                          "solver_called": False, "checker_called": False, "source_admission_verified": False}))
        raise SystemExit(1)
    print(json.dumps({"schema": SCHEMA, "status": result["status"], "output": str(args.output.absolute()),
                      "source_admission": result["source_admission"]}))
    raise SystemExit(result["exit_code"])


if __name__ == "__main__":
    main()
