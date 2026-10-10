#!/usr/bin/env python3
"""Bounded supplied-fit bank/natural rooted-law component with native replay.

--request PATH --output NEWDIR --binary PATH [--expected-binary-sha256 SHA]
[--operation bank|readout] (default readout)

The native check is a separate bounded replay of the same implementation.
No generic independent source-equation or forward-law checker is installed by
this adapter. Source provenance/admission, timed laws and certificates stay false.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time

import native_component as transport

HERE = Path(__file__).resolve().parent
ROOT = transport.ROOT
SCHEMA = "rust_source_fit_component_result_v1"
TRANSPORT_SHA = "cbad55d031621f8e6d29ddc58d6156188c6b9344705d4612642b2423ca6aea3c"
INHERITED_PINS = [
    ("research/2026-10-04-dot-practical-solver-recovery-1803z/01-exact-source-solver/package/solver.py",
     "42e4353d3033e807e26bc409c724fcdee2a01552a630c9364f428f92f9ffe0db"),
    ("research/2026-10-04-dot-practical-solver-recovery-1803z/01-exact-source-solver/package/verify_certificate.py",
     "525b888190d03c2bf6a510a4aab271ab18fe22fa507821faed9409db142f8840"),
    ("research/2026-10-01-g7-continuous-design/law_compiler.py",
     "eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7"),
]
FALSE_CLAIMS = ("certificate_valid", "source_admission_verified", "source_observation_fit_verified",
    "source_provenance_verified", "timed_readout_verified", "full_code_evaluated",
    "universal_native_refinement_verified", "full_solver_verified", "source_witness_certified",
    "unrestricted_exclusion_certified", "complete_source_registry_verified",
    "observation_law_admission_verified", "statistical_confidence_verified",
    "physical_survival_image_verified", "full_joint_calendar_law_verified")
BANK_FALSE = ("certificate_valid", "full_solver_verified", "source_admission_verified",
    "source_observation_fit_verified", "source_provenance_verified", "timed_readout_verified")
ROOTED_FALSE = BANK_FALSE + ("full_code_evaluated", "universal_native_refinement_verified")
REQUEST_KEYS = {"schema", "context", "vertex_names", "taxon_labels", "hybrid_labels", "copy_labels",
    "variables", "values", "equations", "mechanism", "terminal", "compiler_limits", "limits"}


def strict_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError("Duplicate JSON field: " + key)
            result[key] = value
        return result

    def reject(value):
        raise ValueError("Noninteger/nonfinite JSON number is unsupported: " + value)

    value = json.loads(raw.decode("utf-8"), object_pairs_hook=pairs, parse_float=reject, parse_constant=reject)
    if type(value) is not dict:
        raise ValueError("JSON object required")
    return value


def semantic_request(raw):
    """Representation-only DTO projection; no graph, equation or law evaluator."""
    source = strict_json(raw)
    if set(source) != REQUEST_KEYS or source.get("schema") != "source_fit_request_v1":
        raise ValueError("Exact source_fit_request_v1 envelope required")
    result = dict(source)
    result["schema"] = "source_fit_bank_request_v1"
    result["values"] = []
    for value in source["values"]:
        if type(value) is not dict:
            raise ValueError("Invalid exact-value envelope")
        if value.get("kind") == "RATIONAL" and set(value) == {"kind", "value"}:
            result["values"].append({"kind": "rational", "value": value["value"]})
        elif value.get("kind") == "ALGEBRAIC" and set(value) == {"kind", "polynomial_ascending", "real_root_index"}:
            result["values"].append({**value, "kind": "algebraic"})
        else:
            raise ValueError("Invalid exact-value envelope")
    result["equations"] = []
    for equation in source["equations"]:
        if type(equation) is not dict or set(equation) != {"dimension", "terms"}:
            raise ValueError("Invalid equation envelope")
        terms = []
        for term in equation["terms"]:
            if type(term) is not dict or set(term) != {"powers", "coefficient"}:
                raise ValueError("Invalid sparse-term envelope")
            terms.append([term["powers"], term["coefficient"]])
        result["equations"].append({"dimension": equation["dimension"], "terms": terms})
    return result


def exact_equal(left, right):
    """JSON booleans cannot compare equal to natural indices 0/1."""
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return set(left) == set(right) and all(exact_equal(left[key], right[key]) for key in left)
    if isinstance(left, list):
        return len(left) == len(right) and all(exact_equal(a, b) for a, b in zip(left, right))
    return left == right


def source_identities():
    _, raw = transport.read_regular(HERE / "native_component.py", 1024 * 1024)
    if transport.sha(raw) != TRANSPORT_SHA:
        raise ValueError("Pinned shared native transport source changed")
    observed = transport.source_identities()
    package = HERE / "calendar-cli"
    paths = [HERE / "Cargo.toml", HERE / "Cargo.lock", package / "Cargo.toml", package / "Cargo.lock",
        *sorted(package.glob("src/*.rs")), Path(__file__), HERE / "native_component.py"]
    observed["source_fit_frontend_and_adapter_observed"] = [{"path": str(path.relative_to(ROOT)),
        "sha256": transport.sha(transport.read_regular(path, 4 * 1024 * 1024)[1])} for path in paths]
    inherited = []
    for name, digest in INHERITED_PINS:
        _, data = transport.read_regular(ROOT / name, 4 * 1024 * 1024)
        if transport.sha(data) != digest:
            raise ValueError("Attributed source-fit provider identity changed: " + name)
        inherited.append({"path": name, "sha256": digest})
    observed["source_fit_attributed_provider_pins"] = inherited
    observed["python_runtime_observed"] = {"executable": sys.executable, "version": sys.version,
        "claim": "Observed interpreter path/version, not universal interpreter verification."}
    observed["claim"] = ("Attributed provider/transport pins checked, owned source bytes observed. "
        "An optional expected binary digest is checked separately. "
        "These observations do not prove an arbitrary supplied executable was built from those sources.")
    return observed


def recheck_sources(observed):
    for group in ("owned_observed", "source_fit_frontend_and_adapter_observed", "source_fit_attributed_provider_pins"):
        for entry in observed[group]:
            _, raw = transport.read_regular(ROOT / entry["path"], 4 * 1024 * 1024)
            if transport.sha(raw) != entry["sha256"]:
                raise ValueError("Source bytes changed during execution: " + entry["path"])
    for entry in observed["inherited"]["files"]:
        _, raw = transport.read_regular(ROOT / entry["path"], 4 * 1024 * 1024)
        if transport.sha(raw) != entry["sha256"]:
            raise ValueError("Inherited source bytes changed during execution: " + entry["path"])


def validate_bank(frame, expected):
    common = {"certificate_valid", "full_solver_verified", "request", "schema", "source_admission_verified",
        "source_observation_fit_verified", "source_provenance_verified", "status", "supplied_trace_checked", "timed_readout_verified"}
    status = frame.get("status")
    extra = {"SYMBOLIC_BANK": "bank", "UNKNOWN": "limit", "UNSUPPORTED": "reason"}.get(status)
    if frame.get("schema") != "source_fit_bank_result_v1" or extra is None or set(frame) != common | {extra}:
        raise ValueError("Invalid supplied-bank result envelope")
    if not exact_equal(frame["request"], expected) or any(frame.get(key) is not False for key in BANK_FALSE):
        raise ValueError("Bank changed request binding or scientific scope")
    if frame["supplied_trace_checked"] is not (status == "SYMBOLIC_BANK"):
        raise ValueError("Bank trace flag and status disagree")
    return status


def natural_readout_request(expected):
    return {"observer": "ROOTED_UNRANKED_COMPLETE", "forget_configuration_label": True,
        "program": [{"label": "natural", "weight": "1/1", "forcing": [None] * len(expected["context"]["hybrids"])}],
        "word_limits": {"initial_assignments": 16, "initial_terms": 256, "queries": 4096,
            "branches": 65536, "term_products": 262144, "destinations": 4096, "terms": 65536},
        "provider_limits": {
            "epoch": {"calls": 4096, "destinations": 4096, "lifted_terms": 65536, "branches": 4096, "term_products": 65536},
            "boundary": {"assignments": 16, "destinations": 16, "term_contributions": 128},
            "completion": {"calls": 4096, "destinations": 4096, "lifted_terms": 65536}},
        "limits": {"word_rows": 4096, "monomial_contributions": 262144, "normalized_terms": 65536,
            "arithmetic_steps": 1000000, "rational_bits": 4096, "power_exponent": 4096}}


def validate_frame(frame, expected, operation, exit_code):
    """Check framing/bindings only. Native replay is not independent arithmetic."""
    schema, status = frame.get("schema"), frame.get("status")
    if schema == "source_fit_error_v1":
        if set(frame) != {"schema", "status", "code"} or type(frame["code"]) is not str or not frame["code"]:
            raise ValueError("Invalid source-fit error envelope")
        expected_exit = {"INVALID_REQUEST": 1, "INTERNAL": 1, "EXECUTION_FAILURE": 1, "UNKNOWN": 2}.get(status)
    elif schema == "source_fit_bank_result_v1":
        status = validate_bank(frame, expected)
        if operation == "readout" and status == "SYMBOLIC_BANK":
            raise ValueError("Readout producer returned only a successful bank")
        expected_exit = {"SYMBOLIC_BANK": 0, "UNKNOWN": 2, "UNSUPPORTED": 2}[status]
    elif schema == "source_fit_rooted_result_v1" and operation == "readout":
        common = {"schema", "status", "observer", "bank_result", "readout_request", "work", *ROOTED_FALSE}
        extras = {"TABLE": {"configurations", "mixture"}, "UNKNOWN": {"limit"}, "UNSUPPORTED": {"reason"}}.get(status)
        if extras is None or set(frame) != common | extras or frame.get("observer") != "ROOTED_UNRANKED_COMPLETE":
            raise ValueError("Invalid completed-rooted result envelope")
        if any(frame.get(key) is not False for key in ROOTED_FALSE):
            raise ValueError("Rooted producer promoted an unestablished scientific claim")
        if type(frame["bank_result"]) is not dict or validate_bank(frame["bank_result"], expected) != "SYMBOLIC_BANK":
            raise ValueError("Rooted result omits its checked supplied bank")
        if not exact_equal(frame["readout_request"], natural_readout_request(expected)):
            raise ValueError("Rooted producer changed the natural observer/program/effective limits")
        expected_exit = {"TABLE": 0, "UNKNOWN": 2, "UNSUPPORTED": 2}[status]
    else:
        raise ValueError("Unexpected source-fit producer schema")
    if expected_exit is None or exit_code != expected_exit:
        raise ValueError("Producer status and exit code violate the source-fit contract")
    return status


def child_ok(receipt, exit_code):
    return receipt["process_started"] and not receipt["timed_out"] and receipt["exit_code"] == exit_code


def execute(request, output, binary, expected_binary_sha256=None, *, operation="readout"):
    if operation not in ("bank", "readout"):
        raise ValueError("Unsupported source-fit component operation")
    output = Path(output).absolute()
    output.mkdir(parents=True, exist_ok=False)
    component = output / "component"
    component.mkdir()
    native = component / "native"
    native.mkdir()
    result = {"schema": SCHEMA, "operation": operation.upper(), "execution_mode": "FRESH_COMPONENT_EXECUTION",
        "status": "REFUSED_REQUEST", "solver_called": False, "checker_called": False,
        "reference_checker_called": False, "independent_all_coefficients_checked": False,
        "native_replay_verified": False, "supplied_trace_checked": False, "rooted_law_evaluated": False,
        **dict.fromkeys(FALSE_CLAIMS, False), "source_admission": "SOURCE_ADMISSION_NOT_ESTABLISHED",
        "native_checker_mode": "COMPLETE_BOUNDED_NATIVE_REPLAY", "native_checker_algorithm_independent": False,
        "provider_work_checked": False, "provider_exhaustion_verified": False,
        "scope": "One supplied rational survival assignment/equation trace and shared symbolic logarithmic rate bank. "
                 "Optional natural completed rooted-unranked law; no general equation provenance, admitted source fit, "
                 "algebraic RootOf evaluation, timed history, full-Code evaluated law, confidence or full solver claim.",
        "binary_expected_sha256": expected_binary_sha256, "binary_pin_verification": "NOT_REQUESTED_OBSERVED_HASH_ONLY",
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    exit_code = 1
    try:
        if expected_binary_sha256 is not None and not transport.HEX.fullmatch(expected_binary_sha256):
            raise ValueError("Expected binary SHA256 must be 64 lowercase hexadecimal characters")
        request_path, raw = transport.read_regular(request, transport.MAX_REQUEST_BYTES)
        result.update(request_path=str(request_path), request_sha256=transport.sha(raw))
        staged_request = output / "REQUEST.json"
        staged_request.write_bytes(raw)
        expected = semantic_request(raw)
        observed = source_identities()
        (output / "SOURCE-IDENTITIES.json").write_text(json.dumps(observed, sort_keys=True, indent=2) + "\n")
        binary_path, binary_bytes = transport.read_regular(binary, transport.MAX_BINARY_BYTES)
        digest = transport.sha(binary_bytes)
        result.update(binary_path=str(binary_path), binary_observed_sha256=digest, supplied_binary_source_build_verified=False)
        if expected_binary_sha256 is not None:
            if digest != expected_binary_sha256:
                result["binary_pin_verification"] = "MISMATCH_REFUSED_BEFORE_LAUNCH"
                raise ValueError("Supplied binary does not match expected SHA256")
            result["binary_pin_verification"] = "EXPECTED_PIN_MATCHED"
        staged_binary = native / "source-fit-solver"
        staged_binary.write_bytes(binary_bytes)
        staged_binary.chmod(0o700)
        producer = transport.run_child([staged_binary, operation], component, "solver", raw)
        result.update(solver_called=producer["process_started"], solver_execution=producer)
        result["status"] = "RESOURCE_OR_EXECUTION_FAILURE"
        if not producer["process_started"] or producer["timed_out"] or producer["exit_code"] not in (0, 1, 2):
            result["failure_reason"] = "PRODUCER_EXECUTION_FAILED"
        else:
            _, response_bytes = transport.read_regular(component / "solver.stdout", transport.MAX_CERTIFICATE_BYTES)
            frame = strict_json(response_bytes)
            status = validate_frame(frame, expected, operation, producer["exit_code"])
            staged_response = output / "NATIVE-RESULT.json"
            staged_response.write_bytes(response_bytes)
            result.update(native_status=status, native_result_sha256=transport.sha(response_bytes))
            if status in ("INTERNAL", "EXECUTION_FAILURE"):
                result["failure_reason"] = status
            elif status == "INVALID_REQUEST":
                result.update(status="REFUSED_REQUEST", refusal=frame)
            else:
                checker_command = "check" if operation == "bank" else "check-readout"
                checker = transport.run_child([staged_binary, checker_command, staged_request, staged_response], component, "checker")
                result.update(checker_called=checker["process_started"], checker_execution=checker)
                if child_ok(checker, 0) and (component / "checker.stdout").read_bytes() == b'{"schema":"source_fit_check_v1","status":"ACCEPT"}\n':
                    recheck_sources(observed)
                    if transport.sha(staged_binary.read_bytes()) != digest or staged_request.read_bytes() != raw or staged_response.read_bytes() != response_bytes:
                        raise ValueError("Staged request, executable or result changed during execution")
                    result.update(native_replay_verified=True, source_identity_recheck_stable=True,
                        staged_identity_recheck_stable=True, semantic_request_echo_checked=frame.get("schema") != "source_fit_error_v1")
                    if status == "SYMBOLIC_BANK":
                        result.update(status="SUPPLIED_FIT_BANK", supplied_trace_checked=True)
                        exit_code = 0
                    elif status == "TABLE":
                        result.update(status="SUPPLIED_FIT_ROOTED_LAW", supplied_trace_checked=True, rooted_law_evaluated=True)
                        exit_code = 0
                    else:
                        result.update(status=status, unknown_or_unsupported_metadata=frame,
                            unknown_mathematical_exclusion=False, supplied_trace_checked=frame.get("schema") == "source_fit_rooted_result_v1")
                        exit_code = 2
                else:
                    result["failure_reason"] = "NATIVE_REPLAY_REJECTED"
    except (ValueError, OSError, UnicodeError, KeyError, OverflowError, TypeError, IndexError, RecursionError) as error:
        result.update(error_type=type(error).__name__, error=str(error))
        if result["solver_called"]:
            result.update(status="RESOURCE_OR_EXECUTION_FAILURE", failure_reason="INVALID_PRODUCER_OR_CHECKER_OUTPUT")
    finally:
        result.update(exit_code=exit_code, ended_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        (output / "RESULT.json").write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
        (output / "REPORT.md").write_text(
            f"# Supplied source-fit bridge\n\nStatus: **{result['status']}**.\n\n{result['scope']}\n\n"
            f"Producer started: {result['solver_called']}; native replay started: {result['checker_called']}.\n\n"
            "Native replay is the same bounded implementation. No independent general source-law check, "
            "source admission, timed law or mathematical certificate is promoted.\n")
        files = sorted(path for path in output.rglob("*") if path.is_file())
        artifacts = [{"path": str(path.relative_to(output)), "bytes": path.stat().st_size,
            "sha256": transport.sha(path.read_bytes())} for path in files]
        (output / "ARTIFACTS.json").write_text(json.dumps(artifacts, sort_keys=True, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--expected-binary-sha256")
    parser.add_argument("--operation", choices=("bank", "readout"), default="readout")
    args = parser.parse_args()
    try:
        result = execute(args.request, args.output, args.binary, args.expected_binary_sha256, operation=args.operation)
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
