#!/usr/bin/env python3
"""Bounded supplied-fit bank/natural rooted-law component with native replay.

--request PATH --output NEWDIR --binary PATH [--expected-binary-sha256 SHA]
[--operation bank|readout] (default readout)
[--reference-python PATH] (readout only)

The native check is a separate bounded replay of the same implementation.
An optional isolated reference compares all natural rooted-law coefficients and
probabilities using the captured attributed compiler. Source equation provenance,
admission, timed laws and certificates stay false.
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
REFERENCE_HELPER_SHA = "ca7f78096a55a962573cdd5490cc9609f9462035f6e7ca864d1eb050ef46dfbb"
BASELINE_SHA = "eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7"
BACKEND_REQUIREMENTS = {"sympy": "1.14.0", "mpmath": "1.3.0"}
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
    for group in ("owned_observed", "source_fit_frontend_and_adapter_observed", "source_fit_attributed_provider_pins",
                  "source_fit_reference_sources"):
        for entry in observed.get(group, ()):
            _, raw = transport.read_regular(ROOT / entry["path"], 4 * 1024 * 1024)
            if transport.sha(raw) != entry["sha256"]:
                raise ValueError("Source bytes changed during execution: " + entry["path"])
    for entry in observed["inherited"]["files"]:
        _, raw = transport.read_regular(ROOT / entry["path"], 4 * 1024 * 1024)
        if transport.sha(raw) != entry["sha256"]:
            raise ValueError("Inherited source bytes changed during execution: " + entry["path"])


def capture_reference(component):
    """Capture pinned text; execute no checker/provider or scientific import here."""
    specs = [
        ("certificate_check", HERE.parent / "design/certificate_check.py", transport.EXPECTED_FRACTION_HELPER_SHA),
        ("chart_check", HERE.parent / "design/chart_check.py", transport.EXPECTED_CHART_FRACTION_HELPER_SHA),
        ("pinned_source_fit_reference", HERE.parent / "design/source_fit_reference_v2.py", REFERENCE_HELPER_SHA),
        ("pinned_oct1_law_compiler", ROOT / INHERITED_PINS[2][0], BASELINE_SHA),
    ]
    captured = component / "reference-sources"
    captured.mkdir()
    buffers, identities, staged = [], [], []
    for name, path, digest in specs:
        _, raw = transport.read_regular(path, 1024 * 1024)
        if transport.sha(raw) != digest:
            raise ValueError("Pinned source-fit reference source changed: " + str(path))
        target = captured / (name + ".py")
        target.write_bytes(raw)
        buffers.append((name, raw))
        staged.append((target, digest))
        identities.append({"module": name, "path": str(path.relative_to(ROOT)), "sha256": digest,
            "staged_path": str(target.relative_to(component))})
    # Explicit sources are embedded, not imported from mutable repository paths.
    stage = ("import sys, types, json, hashlib\nfrom pathlib import Path\n"
        "runtime_path = Path('REFERENCE-RUNTIME.json')\n"
        "runtime = {'schema': 'source_fit_reference_runtime_v1', 'backend_called': False, 'packages': {},\n"
        "    'interpreter': {'executable': sys.executable, 'version': sys.version,\n"
        "        'executable_sha256': hashlib.sha256(Path(sys.executable).read_bytes()).hexdigest()},\n"
        f"    'requirements': {BACKEND_REQUIREMENTS!r},\n"
        "    'claim': 'Observed executable/package versions, origins and initializer hashes; no universal interpreter or entire third-party runtime verification.'}\n"
        "def save_runtime():\n"
        "    runtime_path.write_text(json.dumps(runtime, sort_keys=True, indent=2)+'\\n')\n"
        "save_runtime()\n")
    for name, raw in buffers[:3]:
        stage += (f"module = types.ModuleType({name!r})\nmodule.__file__ = __file__\n"
            f"sys.modules[{name!r}] = module\n"
            f"source = {raw!r}\n"
            f"if hashlib.sha256(source).hexdigest() != {transport.sha(raw)!r}:\n"
            "    raise ValueError('Captured reference source digest mismatch')\n"
            f"exec(compile(source, {name!r}, 'exec'), module.__dict__)\n")
    stage += ("helper = module\n"
        "helper.BASELINE_PATH = Path(__file__).with_name('__NO_MUTABLE_BASELINE_ALLOWED__')\n"
        "try:\n"
        "    certificate = Path(sys.argv[sys.argv.index('--certificate')+1])\n"
        "    frame = helper.json_frame(helper.read_bounded(certificate, helper.MAX_CERTIFICATE_BYTES), helper.MAX_CERTIFICATE_BYTES)\n"
        "    if type(frame) is dict and frame.get('schema') == 'source_fit_rooted_result_v1' and frame.get('status') == 'TABLE':\n"
        "        runtime['backend_called'] = True\n"
        "        save_runtime()\n"
        "        import sympy, mpmath\n"
        "        for package in (sympy, mpmath):\n"
        "            path = Path(package.__file__)\n"
        "            runtime['packages'][package.__name__] = {'version': package.__version__, 'origin': str(path),\n"
        "                'initializer_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}\n"
        "        save_runtime()\n"
        "        if any(runtime['packages'][name]['version'] != version for name, version in runtime['requirements'].items()):\n"
        "            raise ValueError('Source-fit reference backend version mismatch')\n"
        f"        helper.install_baseline({buffers[3][1]!r})\n"
        "    sys.exit(helper.main())\n"
        "except (ValueError, TypeError, KeyError, IndexError, UnicodeError, OverflowError, RecursionError, OSError, ImportError) as error:\n"
        "    print(json.dumps({'verification_schema': 'source_fit_reference_check_v1', 'result_valid': False,\n"
        "        'error': str(error)[:512], 'certificate_valid': False, 'full_solver_verified': False}, sort_keys=True))\n"
        "    sys.exit(1)\n")
    target = component / "source_fit_reference_staged.py"
    raw = stage.encode("utf-8")
    target.write_bytes(raw)
    staged.append((target, transport.sha(raw)))
    return target, identities, staged


def observe_interpreter(path):
    requested = Path(path).absolute()
    resolved = requested.resolve(strict=True)
    _, raw = transport.read_regular(resolved, transport.MAX_BINARY_BYTES)
    return {"requested_path": str(requested), "resolved_path": str(resolved), "sha256": transport.sha(raw),
        "claim": "Observed executable identity; no externally trusted interpreter pin or universal runtime verification."}


def run_reference(result, command, component, raw, response_bytes, native_status, producer_exit, interpreter, staged):
    reference = transport.run_child([command, "-I", "-B", staged[0], "--request", staged[1],
        "--certificate", staged[2], "--exit-code", str(producer_exit)], component, "reference-checker")
    result.update(reference_checker_called=reference["process_started"], reference_checker_execution=reference,
        reference_result_sha256=reference["stdout_sha256"])
    if not child_ok(reference, 0):
        result["failure_reason"] = "REFERENCE_CHECKER_EXECUTION_FAILED_OR_REJECTED"
        raise ValueError("Requested source-fit reference did not accept")
    _, checked_bytes = transport.read_regular(component / "reference-checker.stdout", transport.MAX_CERTIFICATE_BYTES)
    result["reference_result_sha256"] = transport.sha(checked_bytes)
    if result["reference_result_sha256"] != reference["stdout_sha256"]:
        raise ValueError("Reference result changed after execution receipt")
    checked = strict_json(checked_bytes)
    false = (*ROOTED_FALSE, "provider_work_checked", "bank_metadata_independently_checked", "resource_exhaustion_verified")
    if (checked.get("verification_schema") != "source_fit_reference_check_v1" or checked.get("status") != native_status
            or checked.get("result_valid") is not True or checked.get("request_sha256") != transport.sha(raw)
            or checked.get("response_sha256") != transport.sha(response_bytes)
            or checked.get("baseline_source_sha256") != BASELINE_SHA
            or any(checked.get(key) is not False for key in false)):
        raise ValueError("Reference result changed request/result binding or scientific scope")
    table = native_status == "TABLE"
    for key in ("baseline_called", "independent_all_coefficients_checked", "independent_probabilities_checked",
                "supplied_trace_arithmetic_checked"):
        if checked.get(key) is not table:
            raise ValueError("Reference mathematical flags disagree with TABLE/frame-only scope")
    if native_status != "UNKNOWN" or checked.get("scope") != "OPERATIONAL_FRAME_ONLY":
        if checked.get("request_echo_checked") is not True:
            raise ValueError("Reference omitted semantic request echo check")
    _, runtime_bytes = transport.read_regular(component / "REFERENCE-RUNTIME.json", 1024 * 1024)
    runtime = strict_json(runtime_bytes)
    if (runtime.get("schema") != "source_fit_reference_runtime_v1" or runtime.get("backend_called") is not table
            or runtime.get("requirements") != BACKEND_REQUIREMENTS
            or runtime.get("interpreter", {}).get("executable_sha256") != interpreter["sha256"]):
        raise ValueError("Reference interpreter/backend identity metadata changed")
    packages = runtime.get("packages")
    if type(packages) is not dict or set(packages) != (set(BACKEND_REQUIREMENTS) if table else set()):
        raise ValueError("Reference package observations disagree with actual backend use")
    for name, package in packages.items():
        if (type(package) is not dict or package.get("version") != BACKEND_REQUIREMENTS[name]
                or type(package.get("origin")) is not str or not package["origin"]
                or not transport.HEX.fullmatch(package.get("initializer_sha256", ""))):
            raise ValueError("Reference package origin/version metadata is invalid")
    (component / "REFERENCE-CHECK.json").write_bytes(checked_bytes)
    result.update(reference_check=checked, reference_frame_checked=True, reference_runtime_observed=runtime,
        reference_runtime_sha256=transport.sha(runtime_bytes), reference_baseline_called=table,
        independent_all_coefficients_checked=table, independent_probabilities_checked=table,
        supplied_trace_arithmetic_checked=table)


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


def execute(request, output, binary, expected_binary_sha256=None, *, operation="readout", reference_python=None):
    if operation not in ("bank", "readout"):
        raise ValueError("Unsupported source-fit component operation")
    if reference_python is not None and operation != "readout":
        raise ValueError("Independent rooted-law reference is available for readout only")
    output = Path(output).absolute()
    output.mkdir(parents=True, exist_ok=False)
    component = output / "component"
    component.mkdir()
    native = component / "native"
    native.mkdir()
    result = {"schema": SCHEMA, "operation": operation.upper(), "execution_mode": "FRESH_COMPONENT_EXECUTION",
        "status": "REFUSED_REQUEST", "solver_called": False, "checker_called": False,
        "reference_checker_called": False, "independent_all_coefficients_checked": False,
        "independent_probabilities_checked": False, "supplied_trace_arithmetic_checked": False,
        "reference_requested": reference_python is not None, "reference_frame_checked": False,
        "reference_baseline_called": False, "reference_identity_recheck_stable": False,
        "reference_checker_mode": "PINNED_ORIGINAL_FRONTIER_COEFFICIENT_COMPARISON" if reference_python is not None else "NOT_REQUESTED",
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
        reference_path, reference_staged, interpreter = None, [], None
        if reference_python is not None:
            reference_path, observed["source_fit_reference_sources"], reference_staged = capture_reference(component)
            result["reference_staged_sha256"] = transport.sha(reference_path.read_bytes())
            result["reference_source_pins"] = observed["source_fit_reference_sources"]
            result["reference_backend_requirements"] = BACKEND_REQUIREMENTS
            try:
                interpreter = observe_interpreter(reference_python)
            except (ValueError, OSError) as error:
                result.update(status="RESOURCE_OR_EXECUTION_FAILURE", failure_reason="REFERENCE_INTERPRETER_UNAVAILABLE")
                raise ValueError("Requested reference interpreter is unavailable: " + str(error)) from error
            result["reference_interpreter_observed"] = interpreter
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
                    if reference_python is not None:
                        run_reference(result, interpreter["requested_path"], component, raw, response_bytes, status,
                            producer["exit_code"], interpreter, (reference_path, staged_request, staged_response))
                    recheck_sources(observed)
                    if transport.sha(staged_binary.read_bytes()) != digest or staged_request.read_bytes() != raw or staged_response.read_bytes() != response_bytes:
                        raise ValueError("Staged request, executable or result changed during execution")
                    if reference_python is not None:
                        if not exact_equal(observe_interpreter(reference_python), interpreter):
                            raise ValueError("Reference interpreter bytes or target changed during execution")
                        for path, pinned in reference_staged:
                            if transport.sha(transport.read_regular(path, 1024 * 1024)[1]) != pinned:
                                raise ValueError("Captured reference source/bootstrap changed during execution")
                        result["reference_identity_recheck_stable"] = True
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
            result["status"] = "RESOURCE_OR_EXECUTION_FAILURE"
            result.setdefault("failure_reason", "INVALID_PRODUCER_OR_CHECKER_OUTPUT")
    finally:
        result.update(exit_code=exit_code, ended_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        (output / "RESULT.json").write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
        (output / "REPORT.md").write_text(
            f"# Supplied source-fit bridge\n\nStatus: **{result['status']}**.\n\n{result['scope']}\n\n"
            f"Producer started: {result['solver_called']}; native replay started: {result['checker_called']}; "
            f"optional independent reference started: {result['reference_checker_called']}.\n\n"
            "Native replay uses the same bounded implementation. A requested independent TABLE check compares "
            "all rooted coefficients and probabilities against the captured attributed compiler. Frame-only checks "
            "verify no resource exhaustion. Source-equation provenance, source admission, timed law and mathematical "
            "certificate flags remain false. Interpreter/package identities are observations, not universal runtime verification.\n")
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
    parser.add_argument("--reference-python", type=Path)
    args = parser.parse_args()
    try:
        result = execute(args.request, args.output, args.binary, args.expected_binary_sha256,
            operation=args.operation, reference_python=args.reference_python)
    except (ValueError, OSError) as error:
        print(json.dumps({"schema": SCHEMA, "status": "REFUSED_REQUEST", "error": str(error),
            "solver_called": False, "checker_called": False, "reference_checker_called": False,
            "independent_all_coefficients_checked": False, "independent_probabilities_checked": False,
            **dict.fromkeys(FALSE_CLAIMS, False)}))
        return 1
    print(json.dumps({"schema": SCHEMA, "status": result["status"], "output": str(args.output.absolute()),
        "certificate_valid": False, "source_admission_verified": False, "full_solver_verified": False}))
    return result["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
