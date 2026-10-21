"""Pure RC1 AFFINE value projection; SOURCE ONLY, UNEXECUTED.

Reuses the existing native engine and checked finite-matrix Lean receiver.
No process, solver, path writer or native-origin authentication is implemented.
Call with the hash-authenticated original certificates.py error/schema helpers.
"""
from fractions import Fraction
import hashlib
import re

MAX_REQUEST = 65536
MAX_CERTIFICATE = 4 * 1024**2
VALUE_BITS = 2048
NATIVE_BINARY_SHA256 = "235520d47eaa95873729f2aa60b6f596f41859f1b1807ee58aeb1bd2ab0f876a"
RESTORED_MANIFEST_SHA256 = "c5c84b5fa1755ae05830059353c184a77c52bd236b4053fe2668e6e30f066da6"
NATURAL = re.compile(r"(?:0|[1-9][0-9]*)\Z", re.ASCII)
RATIONAL = re.compile(r"-?(?:0|[1-9][0-9]*)/[1-9][0-9]*\Z", re.ASCII)


class Budget(ValueError):
    """Adapter/source arithmetic budget; never an infeasibility result."""


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(q):
    return str(q.numerator) + "/" + str(q.denominator)


def _bounded(q):
    if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > VALUE_BITS:
        raise Budget("AFFINE adapter arithmetic exceeds 2048 bits")
    return q


def _sum_products(left, right):
    total = Fraction(0)
    for a, b in zip(left, right):
        total = _bounded(total + _bounded(a * b))
    return total


def _ascii(raw, cap, label, checker):
    checker.require(type(raw) is bytes and 0 < len(raw) <= cap, label + " byte cap")
    checker.require(raw.endswith(b"\n") and all(b == 10 or 32 <= b <= 126 for b in raw),
                    label + " requires printable ASCII and one final newline")
    return raw.decode("ascii")


def _fields(line, checker):
    checker.require(line and not line.startswith(" ") and not line.endswith(" ") and
                    "  " not in line, "RC1 exact single-space fields required")
    return line.split(" ")


def _natural(token, maximum, checker):
    checker.require(type(token) is str and len(token) <= len(str(maximum)) and
                    NATURAL.fullmatch(token), "RC1 canonical natural required")
    value = int(token)
    checker.require(value <= maximum, "RC1 natural limit")
    return value


def _rational(token, original_input, checker):
    checker.require(RATIONAL.fullmatch(token) and not token.startswith("-0/"),
                    "RC1 canonical p/q required")
    numerator, denominator = token.split("/")
    magnitude = numerator.removeprefix("-")
    if original_input:
        checker.require(len(magnitude) <= 78 and len(denominator) <= 78,
                        "RC1 original rational magnitude limit")
    elif max(len(magnitude), len(denominator)) > 617:
        raise Budget("AFFINE adapter rational exceeds 2048-bit decimal budget")
    value = Fraction(int(numerator), int(denominator))
    checker.require(canonical(value) == token, "RC1 rational must be reduced with positive denominator")
    if original_input:
        checker.require(max(abs(value.numerator).bit_length(), value.denominator.bit_length()) <= 256,
                        "RC1 original rational exceeds 256 bits")
    return _bounded(value)


def request(raw, checker):
    text = _ascii(raw, MAX_REQUEST, "RC1 request", checker)
    lines = text[:-1].split("\n")
    header = _fields(lines[0], checker)
    checker.require(len(header) == 5 and header[:2] == ["RC1", "AFFINE"],
                    "existing RC1 AFFINE header required")
    n = _natural(header[2], 8, checker)
    m = _natural(header[3], 64, checker)
    cap = _natural(header[4], 4096, checker)
    checker.require(len(lines) == m + 1, "RC1 original row count")
    rows = []
    for line in lines[1:]:
        f = _fields(line, checker)
        checker.require(len(f) == n + 2 and f[0] in ("LE", "LT"), "RC1 row shape")
        rows.append({"strict": f[0] == "LT",
                     "bound": _rational(f[1], True, checker),
                     "coefficients": [_rational(t, True, checker) for t in f[2:]]})
    return {"dimension": n, "rows": rows, "projection_cap": cap,
            "literal_request_sha256": sha(raw)}


def _vector(line, label, size, checker):
    f = _fields(line, checker)
    checker.require(len(f) == size + 2 and f[0] == label and
                    _natural(f[1], 4096, checker) == size, "RC1 certificate vector shape")
    return [_rational(t, False, checker) for t in f[2:]]


def decode(request_literal, certificate_literal, checker):
    """Independently check one supplied finite value certificate in RAM.

    Native/parser refinement and physical row provenance are not inferred.
    An UNKNOWN payload remains a non-certificate.
    """
    matrix = request(request_literal, checker)
    text = _ascii(certificate_literal, MAX_CERTIFICATE, "RC1 certificate", checker)
    prefix = "RC1 RESULT AFFINE\nBEGIN_REQUEST\n" + request_literal.decode("ascii") + "END_REQUEST\n"
    checker.require(text.startswith(prefix), "RC1 exact echoed request identity")
    lines = text[len(prefix):-1].split("\n")
    n, rows = matrix["dimension"], matrix["rows"]
    base = {**matrix, "literal_certificate_sha256": sha(certificate_literal),
            "native_runtime_origin_authenticated": False, "physical_source_admission": False,
            "native_parser_refinement_proved": False}
    if lines[0] == "STATUS UNKNOWN":
        checker.require(len(lines) == 3 and lines[2] == "END", "RC1 UNKNOWN shape")
        limit = _fields(lines[1], checker)
        checker.require(len(limit) == 4 and limit[0] == "LIMIT", "RC1 UNKNOWN limit")
        _natural(limit[1], n, checker)
        _natural(limit[2], 18446744073709551615, checker)
        checker.require(_natural(limit[3], 4096, checker) == matrix["projection_cap"],
                        "RC1 UNKNOWN projection cap changed")
        return {**base, "status": "UNKNOWN", "certificate_checked": False}
    if lines[0] == "STATUS SAT":
        checker.require(len(lines) == 4 and lines[3] == "END", "RC1 SAT shape")
        point = _vector(lines[1], "WITNESS", n, checker)
        evaluated = _vector(lines[2], "EVAL", len(rows), checker)
        actual = [_sum_products(r["coefficients"], point) for r in rows]
        checker.require(evaluated == actual, "RC1 reported evaluations differ from original rows")
        checker.require(all(v < r["bound"] if r["strict"] else v <= r["bound"]
                            for r, v in zip(rows, actual)), "RC1 invalid original-row witness")
        return {**base, "status": "CHECKED_FINITE_AFFINE_WITNESS",
                "certificate_checked": True, "point": point, "evaluations": actual}
    checker.require(lines[0] == "STATUS UNSAT" and len(lines) == 5 and lines[4] == "END",
                    "RC1 supplied value certificate shape")
    weights = _vector(lines[1], "MULTIPLIERS", len(rows), checker)
    checker.require(all(w >= 0 for w in weights), "RC1 negative original-row multiplier")
    checker.require(all(_sum_products(weights, [r["coefficients"][j] for r in rows]) == 0
                        for j in range(n)), "RC1 combined coefficients are not zero")
    bound = _sum_products(weights, [r["bound"] for r in rows])
    strict = any(r["strict"] and w > 0 for r, w in zip(rows, weights))
    checker.require(bound < 0 or (bound == 0 and strict), "RC1 invalid finite Farkas exclusion")
    checker.require(lines[2] == "BOUND " + canonical(bound) and
                    lines[3] == "STRICT " + str(int(strict)), "RC1 reported derivation differs")
    return {**base, "status": "CHECKED_FINITE_AFFINE_EXCLUSION",
            "certificate_checked": True, "weights": weights, "bound": bound, "strict": strict}


def bind_checked_return(receiver_literal, certificate_literal, runtime_return, checker):
    """Bind a complete original native_rc1 runtime result, without authenticating origin.

    Caller supplies the real authenticated runtime/MCP return. Keep its full
    result separately even when binding refuses or the adapter budget exhausts.
    """
    receiver = checker.loads(receiver_literal)
    checker.fields(receiver, ["schema", "task", "input"])
    checker.require(receiver["schema"] == "unified_research_solver_v1" and
                    receiver["task"] == "native_rc1", "original native_rc1 receiver required")
    operation = receiver["input"]
    checker.require(type(operation) is dict and operation.get("operation") in ("solve", "check"),
                    "native operation required")
    checker.fields(operation, ["schema", "operation", "request"] +
                   (["certificate"] if operation["operation"] == "check" else []))
    checker.require(operation["schema"] == "native_rc1_operation_v1" and
                    type(operation["request"]) is str and operation["request"].isascii(),
                    "original native operation schema/ASCII request")
    raw = operation["request"].encode("ascii")
    if operation["operation"] == "check":
        checker.require(type(operation["certificate"]) is str and operation["certificate"].isascii() and
                        operation["certificate"].encode("ascii") == certificate_literal,
                        "original check operation certificate changed")
    values = decode(raw, certificate_literal, checker)
    checker.require(values["certificate_checked"], "UNKNOWN is not a mathematical certificate")
    expected_native = "SAT" if "point" in values else "UNSAT"
    expected_status = "CERTIFIED_AFFINE_WITNESS" if "point" in values else "CERTIFIED_AFFINE_EXCLUSION"
    checker.require(type(runtime_return) is dict and runtime_return.get("status") == expected_status and
                    runtime_return.get("request_preserved") is True and
                    runtime_return.get("primary_request_sha256") == sha(receiver_literal) and
                    runtime_return.get("canonical_request_sha256") == checker.digest(receiver) and
                    runtime_return.get("source_feasibility_certified") is False,
                    "complete original runtime request/outcome binding")
    delegate = runtime_return.get("delegate")
    checker.require(type(delegate) is dict and delegate.get("invoked") is True and
                    delegate.get("returned") is True, "complete original delegate return required")
    result = delegate.get("result")
    checker.require(type(result) is dict and result.get("status") == expected_status and
                    result.get("request_sha256") == checker.digest(receiver) and
                    result.get("source_feasibility_certified") is False,
                    "original dispatcher return differs")
    native = result.get("native_result")
    checker.require(type(native) is dict and native.get("schema") == "native_rc1_operation_result_v1" and
                    native.get("status") == expected_status and native.get("native_kind") == "AFFINE" and
                    native.get("operation") == operation["operation"] and
                    native.get("native_status", native.get("supplied_native_status")) == expected_native and
                    native.get("request_sha256") == sha(raw) and
                    native.get("response_sha256") == sha(certificate_literal) and
                    native.get("certificate_checked") is True and
                    native.get("native_checker_algorithm_independent") is True and
                    native.get("physical_source_admission_verified") is False and
                    native.get("source_feasibility_certified") is False and
                    native.get("unknown_size_exclusion_certified") is False and
                    native.get("full_joint_calendar_law_verified") is False and
                    native.get("general_G3_resolved") is False and
                    native.get("native_refinement_proved") is False,
                    "original request-bound native value/checker return differs")
    identity = native.get("runtime")
    checker.require(type(identity) is dict and identity.get("binary_sha256") == NATIVE_BINARY_SHA256 and
                    identity.get("restored_manifest_sha256") == RESTORED_MANIFEST_SHA256,
                    "original selected native runtime identity differs")
    checked_execution = native.get("check_execution")
    checker.require(type(checked_execution) is dict and checked_execution.get("exit_code") == 0 and
                    checked_execution.get("timed_out") is False, "original native check did not finish")
    if operation["operation"] == "solve":
        solved = native.get("solve_execution")
        checker.require(type(solved) is dict and solved.get("exit_code") == 0 and
                        solved.get("timed_out") is False, "original native solve did not finish")
    return {"schema": "bound_original_affine_result_v1", "status": expected_status,
            "literal_receiver_sha256": sha(receiver_literal),
            "literal_request_sha256": sha(raw), "literal_certificate_sha256": sha(certificate_literal),
            "dimension": values["dimension"], "ordered_rows": len(values["rows"]),
            "scope": "one supplied finite rational matrix over the reals",
            "native_runtime_origin_authenticated_by_this_pure_function": False,
            "native_parser_refinement_proved": False, "physical_source_admission": False,
            "complete_original_runtime_return": runtime_return}
