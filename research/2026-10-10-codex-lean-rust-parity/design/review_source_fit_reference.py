#!/usr/bin/env python3
"""Scheduled inherited-reference review of saved source-fit tables and forgeries.

No native executable or compiler is launched. This program executes the pinned
inherited symbolic provider in its own prepared, externally bounded Python
process. It must be scheduled through the sole runtime/compiler coordinator.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
from types import ModuleType

ROOT = Path(__file__).resolve().parents[3]
PARITY = ROOT / "research/2026-10-10-codex-lean-rust-parity"
PINS = (
    ("certificate_check", PARITY / "design/certificate_check.py", "ec55b12c10b8e5fd2eec29f72b4d14138b57d84139239e04e0c8907602e58e24"),
    ("chart_check", PARITY / "design/chart_check.py", "3de5f13954f6aa40b53c0cf5a8b57d8895046becfd36989087fb6ec0748b5e8a"),
    ("source_fit_reference", PARITY / "design/source_fit_reference.py", "0eedff2d9ab21514e3788ae5f9310e33bd57d8ce86e4cf038bb08520ccd99fc6"),
    ("inherited_provider", ROOT / "research/2026-10-01-g7-continuous-design/law_compiler.py", "eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7"),
)
CASES = (
    ("hybrid-common-sat", "63d6b2242c428d98fe89c3c6e6295948026de220095a3fe852d5e66069db6591", "3f21282fe0bdc8ecba4e8d4b4779ce3dfc3677bf4bccf904ff367c760b966039"),
    ("hybrid-independent-sat", "0d3d30b9be0cf8ccbb9473c5fdeffd6a4c6a129fa122fff1ea0b181411dd7ef4", "16bc758e3cc05c9277859bac9c29b3b3586de7ff9d8c379011303ecdef0bcbdb"),
    ("hybrid-common-permuted", "a01f07c1cd2fa5a84880bd46ea7a3890356af9c936ca4873ebd5bb7b5f40875e", "446d2dfb9f66dca6155ffbb48d5a39c3aa7550175441a043cac57457fd59e352"),
)
DEFAULT_SAVED = PARITY / "rust/evidence/source-fit-native-slot-20261010T221453.635194Z/cli-challenges"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def wire(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def qtext(q):
    return f"{q.numerator}/{q.denominator}"


def install_captured(out):
    source = out / "sources"
    source.mkdir()
    captured, entries = {}, []
    for alias, path, digest in PINS:
        raw = path.read_bytes()
        require(sha(raw) == digest, f"checker/provider source changed: {path}")
        target = source / (alias + ".py")
        target.write_bytes(raw)
        captured[alias] = raw
        entries.append({"path": str(path), "sha256": digest, "bytes": len(raw)})
        if alias != "inherited_provider":
            module = ModuleType(alias)
            module.__file__ = str(target)
            sys.modules[alias] = module
            exec(compile(raw, str(target), "exec"), module.__dict__)
    helper = sys.modules["source_fit_reference"]
    helper.BASELINE_PATH = out / "FORBIDDEN_MUTABLE_PROVIDER_FALLBACK"
    helper.install_baseline(captured["inherited_provider"])
    return helper, entries


def add_term(row, powers, delta):
    terms = {tuple(p): Fraction(q) for p, q in row["edge_polynomial"]}
    key = tuple(powers)
    terms[key] = terms.get(key, Fraction(0)) + delta
    if terms[key] == 0:
        del terms[key]
    row["edge_polynomial"] = [[list(power), qtext(coefficient)] for power, coefficient in sorted(terms.items())]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--saved-directory", type=Path, default=DEFAULT_SAVED)
    args = parser.parse_args()
    out = args.output.absolute()
    out.mkdir(parents=True, exist_ok=False)
    results = []
    receipt = {"schema": "source_fit_inherited_reference_review_v1", "status": "FAILED",
               "native_processes_started": 0, "lean_compiler_processes_started": 0,
               "source_admission_verified": False, "timed_readout_verified": False,
               "universal_native_refinement_verified": False, "full_solver_verified": False,
               "scope": "Pinned inherited full-joint coefficient/probability execution against three saved native tables and targeted forgeries."}
    try:
        helper, pins = install_captured(out)
        receipt["source_pins"] = pins
        reference_checks = ("result_valid", "baseline_called", "request_echo_checked",
                            "independent_all_coefficients_checked", "independent_probabilities_checked",
                            "supplied_trace_arithmetic_checked")

        def attempt(name, request, response, expected=True, exit_code=0, error_contains=None, table=True):
            directory = out / name
            directory.mkdir()
            (directory / "REQUEST.json").write_bytes(request)
            (directory / "RESPONSE.json").write_bytes(response)
            try:
                verification = helper.verify_response(request, response, exit_code)
                require(expected, "forgery was accepted")
                if table:
                    require(verification["status"] == "TABLE" and all(verification[k] is True for k in reference_checks),
                            "TABLE lacks actual inherited coefficient verification")
                else:
                    require(verification["status"] == "UNKNOWN" and verification["request_echo_checked"] is True,
                            "UNKNOWN frame was not checked")
                    require(all(verification[k] is False for k in ("baseline_called", "independent_all_coefficients_checked",
                            "independent_probabilities_checked", "supplied_trace_arithmetic_checked", "resource_exhaustion_verified")),
                            "UNKNOWN promoted mathematical/exhaustion claims")
                (directory / "VERIFICATION.json").write_bytes(wire(verification))
                result = {"case": name, "pass": True, "accepted": True, "status": verification["status"]}
                if table:
                    result.update(rows=verification["rooted_outcomes"], terms=verification["whole_edge_terms"])
            except (ValueError, TypeError, KeyError, UnicodeError, OverflowError, RecursionError) as error:
                require(not expected, f"expected accepted case failed: {name}: {error}")
                require(error_contains is None or error_contains in str(error), f"wrong rejection reason: {name}: {error}")
                (directory / "VERIFICATION.json").write_bytes(wire({"rejected": True, "error": str(error)}))
                result = {"case": name, "pass": True, "accepted": False, "error": str(error)}
            result.update(request_sha256=sha(request), response_sha256=sha(response))
            results.append(result)

        saved = []
        for name, input_sha, response_sha in CASES:
            request = (PARITY / f"rust/fixtures/source-fit/{name}.request.json").read_bytes()
            response_path = args.saved_directory / (name + "-readout-file") / "stdout"
            response = response_path.read_bytes()
            require(sha(request) == input_sha and sha(response) == response_sha, f"saved native input/output changed: {name}")
            attempt(name, request, response)
            saved.append((request, response))

        raw_request, raw_response = saved[0]
        request, response = json.loads(raw_request), json.loads(raw_response)
        dimension = len(request["context"]["edges"])
        zero, linear = [0] * dimension, [1] + [0] * (dimension - 1)
        x0, delta = Fraction(request["values"][0]["value"]), Fraction(1, 1000)
        forged = copy.deepcopy(response)
        for target, sign in zip(forged["mixture"][:2], (1, -1)):
            add_term(target, linear, sign * delta)
            add_term(target, zero, -sign * delta * x0)
        forged["configurations"][0]["outcomes"] = copy.deepcopy(forged["mixture"])
        # Changes vanish at this assignment; summed polynomials/mass remain one.
        attempt("balanced_zero_at_assignment_polynomial", raw_request, wire(forged), False,
                error_contains="coefficient table differs")

        forged = copy.deepcopy(response)
        for target, sign in zip(forged["mixture"][:2], (1, -1)):
            target["probability"] = qtext(Fraction(target["probability"]) + sign * delta)
        forged["configurations"][0]["outcomes"] = copy.deepcopy(forged["mixture"])
        attempt("balanced_probability_only", raw_request, wire(forged), False,
                error_contains="probability differs")

        changed_request = copy.deepcopy(request)
        term = changed_request["equations"][0]["terms"][0]
        term["coefficient"] = qtext(Fraction(term["coefficient"]) + 1)
        forged = copy.deepcopy(response)
        forged["bank_result"]["request"] = helper.bank_request(changed_request)
        attempt("spoofed_trace_zero_metadata", wire(changed_request), wire(forged), False,
                error_contains="trace does not vanish")

        attempt("substituted_request", saved[1][0], raw_response, False, error_contains="request echo changed")
        attempt("table_exit_two", raw_request, raw_response, False, exit_code=2, error_contains="status/exit mismatch")
        forged = copy.deepcopy(response)
        forged["bank_result"]["request"]["context"]["root"] = False
        attempt("boolean_root_echo", raw_request, wire(forged), False, error_contains="request echo changed")
        forged = copy.deepcopy(response)
        forged["source_admission_verified"] = True
        attempt("promoted_scientific_gate", raw_request, wire(forged), False, error_contains="was promoted")
        forged = copy.deepcopy(response)
        forged["mixture"][0]["edge_polynomial"][0][1] = "2/4"
        forged["configurations"][0]["outcomes"] = copy.deepcopy(forged["mixture"])
        attempt("noncanonical_coefficient", raw_request, wire(forged), False, error_contains="unreduced rational")
        duplicate = raw_request.replace(b"{", b'{"schema":"source_fit_request_v1",', 1)
        attempt("duplicate_request_key", duplicate, raw_response, False, error_contains="duplicate JSON")

        renamed = copy.deepcopy(request)
        renamed["vertex_names"][renamed["context"]["hybrids"][0][0]] = "H[] + 'caller name'"
        renamed["variables"][-1] = "g_H[] + 'caller name'"
        renamed["copy_labels"] = ["copy,0", "copy(1)", "copy[2]"]
        same_law = copy.deepcopy(response)
        same_law["bank_result"]["request"] = helper.bank_request(renamed)
        attempt("safe_caller_names_reference_invariant", wire(renamed), wire(same_law))

        unknown_request = copy.deepcopy(request)
        unknown_request["limits"]["equations"] = 0
        unknown = {"schema": "source_fit_bank_result_v1", "status": "UNKNOWN",
                   "request": helper.bank_request(unknown_request), "supplied_trace_checked": False,
                   "limit": {"stage": "INPUT", "kind": "equations", "required": "17", "cap": 0},
                   **{k: False for k in helper.FALSE_GATES}}
        attempt("forged_unknown_count_is_frame_only", wire(unknown_request), wire(unknown), True,
                exit_code=2, table=False)

        for alias, path, digest in PINS:
            require(sha(path.read_bytes()) == digest, f"source changed during reference execution: {path}")
        import sympy
        import mpmath
        receipt["runtime_observed"] = {"python_executable": sys.executable, "python_version": sys.version}
        for package in (sympy, mpmath):
            path = Path(package.__file__).resolve()
            receipt["runtime_observed"][package.__name__] = {"version": package.__version__,
                "initializer_path": str(path), "initializer_sha256": sha(path.read_bytes())}
        receipt.update(status="PASS", passed=len(results), controls=results, source_pins_stable=True,
                       saved_native_cases=3, saved_native_rows=sum(r.get("rows", 0) for r in results[:3]),
                       saved_native_terms=sum(r.get("terms", 0) for r in results[:3]))
    except BaseException as error:
        receipt.update(error_type=type(error).__name__, error=str(error), controls=results)
    finally:
        (out / "RECEIPT.json").write_bytes(wire(receipt))
    print(json.dumps({"status": receipt["status"], "receipt": str(out / "RECEIPT.json"), "passed": len(results)}))
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
