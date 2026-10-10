#!/usr/bin/env python3
"""Bounded supplied-calendar table adapter with independent coefficient checks.

--request PATH --output NEWDIR --binary PATH [--expected-binary-sha256 SHA]

The native checker replays the full calculation. The isolated reference child
uses separately captured spectral-generator and copied-carrier algorithms.
Provider UNKNOWN framing is checked without claiming independent exhaustion.
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
SCHEMA = "rust_calendar_component_result_v1"
PINS = [
    ("certificate_check", "ec55b12c10b8e5fd2eec29f72b4d14138b57d84139239e04e0c8907602e58e24"),
    ("chart_check", "3de5f13954f6aa40b53c0cf5a8b57d8895046becfd36989087fb6ec0748b5e8a"),
    ("population_oracle", "216d83a844019f115de1dfa19c12827e0570348181d380f1435dc6ee646748ff"),
    ("epoch_oracle", "da66bf78d538d7acdc8d67b560b3d7fe95fd987d614cf34ffd3803c03c8235bd"),
    ("boundary_oracle", "0d85747a1f58c4c78b4aa7b0a8f671cd145b7a5f4ce990f9ed33df6b4766db29"),
    ("source_word_oracle", "bb9f4470e9a5ca4358e5916d546c9009c9abfb62bfa9fc415f589891bfde5102"),
    ("source_calendar_oracle", "3f01def72cbd1b999099f713764e97941753a12349bcf4e23f3e7d90b63de27c"),
    ("calendar_check", "6190bcd125c51d2e133b571ecc9fe08298fe5a731dc6536459f66446f0ae29bb"),
]
FALSE_CLAIMS = ("certificate_valid", "source_admission_verified", "source_witness_certified",
    "unrestricted_exclusion_certified", "complete_source_registry_verified",
    "observation_law_admission_verified", "statistical_confidence_verified",
    "physical_survival_image_verified", "full_joint_calendar_law_verified", "full_solver_verified")
TABLE_FLAGS = ("formal_table_checked", "independent_all_coefficients_checked",
    "calendar_agenda_checked", "physical_substitutions_checked")


def capture_sources():
    """Pin one read per source and supply every import from those captured bytes."""
    identities, buffers = [], []
    helper = None
    for name, digest in PINS:
        path, raw = transport.read_regular(HERE.parent / "design" / (name + ".py"), 1024 * 1024)
        if transport.sha(raw) != digest:
            raise ValueError("Pinned calendar reference source changed: " + str(path))
        identities.append({"module": name, "path": str(path.relative_to(ROOT)), "sha256": digest})
        buffers.append((name, raw))
        module = ModuleType(name)
        module.__file__ = str(path)
        sys.modules[name] = module
        exec(compile(raw, str(path), "exec"), module.__dict__)
        helper = module
    stage = "import sys, types\n"
    for name, raw in buffers:
        # All imports are registered before the final helper CLI is executed.
        stage += (f"module = types.ModuleType({name!r})\nmodule.__file__ = __file__\n"
                  f"sys.modules[{name!r}] = module\n"
                  f"exec(compile({raw!r}, {name!r}, 'exec'), module.__dict__)\n")
    stage += ("try:\n    sys.exit(module.main())\n"
              "except (ValueError, UnicodeError, OSError, OverflowError, TypeError, KeyError, IndexError) as error:\n"
              "    sys.stdout.buffer.write(module.canonical_json({'result_valid': False, 'certificate_valid': False, 'error': str(error)}))\n"
              "    sys.exit(1)\n")
    return stage.encode("utf-8"), helper, identities


def source_identities(reference_identities):
    observed = transport.source_identities()
    package = HERE / "calendar-cli"
    files = [package / "Cargo.toml", package / "Cargo.lock", *sorted(package.glob("src/*.rs")),
             *sorted(package.glob("tests/*.rs")), Path(__file__), HERE / "native_component.py"]
    observed["calendar_frontend_owned_observed"] = [{"path": str(path.relative_to(ROOT)),
        "sha256": transport.sha(path.read_bytes())} for path in files]
    observed["calendar_reference_sources"] = reference_identities
    observed["python_runtime_observed"] = {"version": sys.version, "executable": sys.executable,
        "claim": "Observed interpreter version and path; no universal interpreter verification."}
    observed["claim"] = ("Captured reference source pins checked; owned frontend/core byte identities observed. "
        "An optional supplied executable digest pin is checked independently. "
        "These observations do not prove the arbitrary supplied executable was built from the observed sources.")
    return observed


def recheck_identities(observed):
    for group in ("owned_observed", "calendar_frontend_owned_observed", "calendar_reference_sources"):
        for entry in observed[group]:
            _, raw = transport.read_regular(ROOT / entry["path"], 4 * 1024 * 1024)
            if transport.sha(raw) != entry["sha256"]:
                raise ValueError("Source bytes changed during component execution: " + entry["path"])
    for entry in observed["inherited"]["files"]:
        if transport.sha((ROOT / entry["path"]).read_bytes()) != entry["sha256"]:
            raise ValueError("Inherited source changed during execution: " + entry["path"])


def child_ok(receipt, code):
    return (receipt["process_started"] and not receipt["timed_out"] and receipt["exit_code"] == code)


def execute(request, output, binary, expected_binary_sha256=None):
    output = Path(output).absolute()
    output.mkdir(parents=True, exist_ok=False)
    component = output / "component"
    component.mkdir()
    native = component / "native"
    native.mkdir()
    result = {"schema": SCHEMA, "operation": "CALENDAR", "execution_mode": "FRESH_COMPONENT_EXECUTION",
        "status": "REFUSED_REQUEST", "solver_called": False, "checker_called": False,
        "reference_checker_called": False, **dict.fromkeys(TABLE_FLAGS, False), **dict.fromkeys(FALSE_CLAIMS, False),
        "source_admission": "SOURCE_ADMISSION_NOT_ESTABLISHED",
        "native_checker_mode": "COMPLETE_BOUNDED_FORWARD_REPLAY", "native_checker_algorithm_independent": False,
        "provider_work_checked": False, "provider_exhaustion_verified": False,
        "scope": "Complete ordered genealogy-state polynomial table for one supplied original-ID graph, "
                 "copied samples, rational calendar and shared physical bank; exact symbolic substitutions. "
                 "Source census, observation fitting, confidence, timed laws and policy completion remain unestablished.",
        "binary_expected_sha256": expected_binary_sha256,
        "binary_pin_verification": "NOT_REQUESTED_OBSERVED_HASH_ONLY",
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    exit_code = 1
    try:
        if expected_binary_sha256 is not None and not transport.HEX.fullmatch(expected_binary_sha256):
            raise ValueError("Expected binary SHA256 must be 64 lowercase hexadecimal characters")
        request_path, raw = transport.read_regular(request, transport.MAX_REQUEST_BYTES)
        result.update(request_path=str(request_path), request_sha256=transport.sha(raw))
        staged_request = output / "REQUEST.json"
        staged_request.write_bytes(raw)
        staged_reference, helper, reference_pins = capture_sources()
        helper.parse_request(raw)
        observed = source_identities(reference_pins)
        observed["staged_reference_sha256"] = transport.sha(staged_reference)
        result["staged_reference_sha256"] = transport.sha(staged_reference)
        (output / "SOURCE-IDENTITIES.json").write_text(json.dumps(observed, indent=2, sort_keys=True) + "\n")
        binary_path, binary_bytes = transport.read_regular(binary, transport.MAX_BINARY_BYTES)
        digest = transport.sha(binary_bytes)
        result.update(binary_path=str(binary_path), binary_observed_sha256=digest,
                      supplied_binary_source_build_verified=False)
        if expected_binary_sha256 is not None:
            if digest != expected_binary_sha256:
                result["binary_pin_verification"] = "MISMATCH_REFUSED_BEFORE_LAUNCH"
                raise ValueError("Supplied binary does not match expected SHA256")
            result["binary_pin_verification"] = "EXPECTED_PIN_MATCHED"
        staged_binary = native / "calendar-solver"
        staged_binary.write_bytes(binary_bytes)
        staged_binary.chmod(0o700)
        reference_path = native / "calendar_check.py"
        reference_path.write_bytes(staged_reference)
        producer = transport.run_child([staged_binary, "solve"], component, "solver", raw)
        result.update(solver_called=producer["process_started"], solver_execution=producer)
        result["status"] = "RESOURCE_OR_EXECUTION_FAILURE"
        if not producer["process_started"] or producer["timed_out"] or producer["exit_code"] not in (0, 2):
            result["failure_reason"] = "PRODUCER_EXECUTION_FAILED"
        else:
            _, table_bytes = transport.read_regular(component / "solver.stdout", transport.MAX_CERTIFICATE_BYTES)
            table = helper.strict_json(table_bytes, transport.MAX_CERTIFICATE_BYTES, canonical=True)
            status = table.get("status")
            if status not in ("TABLE", "UNKNOWN") or producer["exit_code"] != {"TABLE": 0, "UNKNOWN": 2}[status]:
                raise ValueError("Calendar producer status and exit code violate the contract")
            staged_table = output / "TABLE.json"
            staged_table.write_bytes(table_bytes)
            result.update(calendar_status=status, table_sha256=transport.sha(table_bytes))
            checker = transport.run_child([staged_binary, "check", "--request", staged_request,
                "--certificate", staged_table], component, "checker")
            result.update(checker_called=checker["process_started"], checker_execution=checker)
            reference = transport.run_child([sys.executable, "-I", "-B", reference_path,
                "--request", staged_request, "--certificate", staged_table,
                "--exit-code", str(producer["exit_code"])], component, "reference-checker")
            result.update(reference_checker_called=reference["process_started"], reference_checker_execution=reference)
            expected_reference_exit = 0 if status == "TABLE" else 2
            accepted = (child_ok(checker, 0) and (component / "checker.stdout").read_bytes() ==
                b'{"schema":"source_calendar_check_v1","status":"ACCEPT"}\n'
                and child_ok(reference, expected_reference_exit))
            if accepted:
                _, checked_bytes = transport.read_regular(component / "reference-checker.stdout", transport.MAX_CERTIFICATE_BYTES)
                checked = helper.strict_json(checked_bytes, transport.MAX_CERTIFICATE_BYTES, canonical=True)
                accepted = (checked.get("status") == status and checked.get("result_valid") is True
                    and checked.get("request_sha256") == transport.sha(raw)
                    and all(checked.get(key) is False for key in FALSE_CLAIMS if key not in
                            ("source_witness_certified", "unrestricted_exclusion_certified")))
                if status == "TABLE":
                    accepted = accepted and all(checked.get(key) is True for key in TABLE_FLAGS)
            if accepted:
                recheck_identities(observed)
                if transport.sha(staged_binary.read_bytes()) != digest or reference_path.read_bytes() != staged_reference:
                    raise ValueError("Staged executable or reference bytes changed during execution")
                if staged_request.read_bytes() != raw or staged_table.read_bytes() != table_bytes:
                    raise ValueError("Staged request or table changed during execution")
                result.update(source_identity_recheck_stable=True, staged_identity_recheck_stable=True,
                              reference_check=checked)
                if status == "TABLE":
                    result.update(status="SUPPLIED_CALENDAR_TABLE", **dict.fromkeys(TABLE_FLAGS, True))
                    exit_code = 0
                else:
                    result.update(status="UNKNOWN", unknown_metadata=checked,
                        unknown_mathematical_exclusion=False,
                        calendar_agenda_checked=checked["calendar_agenda_checked"],
                        physical_substitutions_checked=checked["physical_substitutions_checked"])
                    exit_code = 2
            else:
                result["failure_reason"] = "NATIVE_REPLAY_OR_INDEPENDENT_REFERENCE_REJECTED"
    except (ValueError, OSError, UnicodeError, KeyError, OverflowError, TypeError, IndexError) as error:
        result.update(error_type=type(error).__name__, error=str(error))
        if result["solver_called"]:
            result.update(status="RESOURCE_OR_EXECUTION_FAILURE", failure_reason="INVALID_PRODUCER_OR_CHECKER_OUTPUT")
    finally:
        result.update(exit_code=exit_code, ended_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        (output / "RESULT.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        (output / "REPORT.md").write_text(
            f"# Supplied-calendar calculation\n\nStatus: **{result['status']}**.\n\n{result['scope']}\n\n"
            f"Producer started: {result['solver_called']}; native replay started: {result['checker_called']}; "
            f"independent reference started: {result['reference_checker_called']}.\n\n"
            "Exact table checks do not establish source admission or a full solver certificate. "
            "Inner provider UNKNOWN is authenticated framing, not an independent exhaustion proof.\n")
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
            "solver_called": False, "checker_called": False, "reference_checker_called": False,
            **dict.fromkeys(FALSE_CLAIMS, False)}))
        return 1
    print(json.dumps({"schema": SCHEMA, "status": result["status"], "output": str(args.output.absolute()),
        "certificate_valid": False, "source_admission_verified": False, "full_solver_verified": False}))
    return result["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
