#!/usr/bin/env python3
"""Independent exact RC1 certificate consumer, using original-row arithmetic.

SAT and UNSAT are checked without Fourier--Motzkin projection, invoking a
solver, or trusting a native binary. UNKNOWN and conditional count produce no
source/feasibility certificate. Original graph/chart admission is external.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
import re
import sys

MAX_REQUEST_BYTES = 65536
MAX_CERTIFICATE_BYTES = 4 * 1024 * 1024
BIT_BOUND = 1 << 256
Q_TOKEN = re.compile(r"(?:0|[1-9][0-9]*|-[1-9][0-9]*)/[1-9][0-9]*\Z")
N_TOKEN = re.compile(r"(?:0|[1-9][0-9]*)\Z")

# Exact derived rationals have no 4,300-digit implementation threshold. Their
# aggregate wire input remains bounded above before any decimal conversion.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def qtext(q):
    q = Fraction(q)
    return f"{q.numerator}/{q.denominator}"


def qparse(token, *, bounded=False):
    require(bool(Q_TOKEN.fullmatch(token)), "noncanonical rational token")
    q = Fraction(token)
    require(qtext(q) == token, "unreduced rational token")
    if bounded:
        require(abs(q.numerator) < BIT_BOUND and q.denominator < BIT_BOUND,
                "input rational exceeds bit cap")
    return q


def nparse(token):
    require(bool(N_TOKEN.fullmatch(token)), "noncanonical natural token")
    return int(token)


@dataclass(frozen=True)
class Row:
    strict: bool
    bound: Fraction
    coeff: tuple[Fraction, ...]


def parse_request(raw):
    require(len(raw) <= MAX_REQUEST_BYTES, "input exceeds byte cap")
    text = raw.decode("ascii")
    require(text.endswith("\n"), "missing final newline")
    lines = text[:-1].split("\n")
    require(all(line and all(line.split(" "))
                and all(c == " " or 33 <= ord(c) <= 126 for c in line)
                for line in lines), "noncanonical whitespace/control character")
    first = lines[0].split(" ")
    require(first[:1] == ["RC1"], "bad version")
    if len(first) == 5 and first[1] == "AFFINE":
        n, m, cap = map(nparse, first[2:])
        require(n <= 8 and m <= 64 and cap <= 4096, "contract dimension or cap exceeded")
        require(len(lines) == m + 1, "wrong number of rows")
        rows = []
        for line in lines[1:]:
            tokens = line.split(" ")
            require(len(tokens) == n + 2 and tokens[0] in ("LE", "LT"), "bad row arity/tag")
            qs = tuple(qparse(t, bounded=True) for t in tokens[1:])
            rows.append(Row(tokens[0] == "LT", qs[0], qs[1:]))
        return "AFFINE", n, tuple(rows), cap
    if len(first) == 6 and first[1] == "COUNT":
        require(len(lines) == 1, "extra COUNT lines")
        qs = tuple(qparse(t, bounded=True) for t in first[2:])
        b, epsilon, sigma, M = qs
        require(b > 0 and epsilon > 0 and sigma > 0 and M >= 0, "invalid count domain")
        return "COUNT", qs
    raise ValueError("unsupported request grammar")


def dot(coeff, vector):
    require(len(coeff) == len(vector), "dot-product dimension mismatch")
    return sum((a * x for a, x in zip(coeff, vector)), Fraction(0))


def holds(row, vector):
    lhs = dot(row.coeff, vector)
    return lhs < row.bound if row.strict else lhs <= row.bound


def check_witness(rows, witness, emitted_lhs=None):
    actual = tuple(dot(row.coeff, witness) for row in rows)
    if emitted_lhs is not None:
        require(actual == tuple(emitted_lhs), "forged original-row evaluation")
    require(all(holds(row, witness) for row in rows), "witness violates an original row")
    return actual


def check_exclusion(n, rows, weights, aggregate, strict):
    require(all(len(row.coeff) == n for row in rows), "wrong original-row dimension")
    require(len(weights) == len(rows), "wrong multiplier dimension")
    require(all(w >= 0 for w in weights), "negative original-row multiplier")
    cancelled = tuple(sum((w * row.coeff[i] for w, row in zip(weights, rows)), Fraction(0))
                      for i in range(n))
    require(all(x == 0 for x in cancelled), "exclusion coefficients do not cancel")
    bound = sum((w * row.bound for w, row in zip(weights, rows)), Fraction(0))
    require(bound == aggregate, "forged aggregate bound")
    actual_strict = any(w > 0 and row.strict for w, row in zip(weights, rows))
    require(actual_strict == strict, "forged exclusion strictness")
    require(bound < 0 or (bound == 0 and actual_strict), "exclusion has no contradiction")


def list_payload(line, tag, count):
    tokens = line.split(" ")
    require(tokens[:1] == [tag] and len(tokens) == count + 2, "bad vector framing")
    require(nparse(tokens[1]) == count, "wrong emitted vector length")
    return tuple(qparse(t) for t in tokens[2:])


def verify_certificate(raw_request, raw_result, exit_code=None):
    """Return checked details, or raise ValueError/UnicodeError on rejection.

    `certificate_valid` is true only for original-row AFFINE SAT/UNSAT evidence.
    If provided, an exit code must match the canonical result semantics.
    """
    require(len(raw_result) <= MAX_CERTIFICATE_BYTES, "result exceeds certificate byte cap")
    try:
        request = parse_request(raw_request)
    except (ValueError, UnicodeError, OverflowError):
        require((exit_code is None or exit_code == 1)
                and raw_result == b"RC1 ERROR INVALID_REQUEST\n",
                "invalid input did not produce canonical refusal")
        return {"status": "REFUSED", "result_valid": True, "certificate_valid": False,
                "source_admission_established": False}
    op = request[0]
    prefix = f"RC1 RESULT {op}\nBEGIN_REQUEST\n".encode() + raw_request + b"END_REQUEST\n"
    require(raw_result.startswith(prefix), "result changed/omitted complete request bytes")
    payload = raw_result[len(prefix):].decode("ascii")
    require(payload.endswith("\n"), "result missing final newline")
    lines = payload[:-1].split("\n")
    require(lines[-1:] == ["END"], "result lacks exact end framing")
    common = {"operation": op, "result_valid": True, "certificate_valid": False,
              "source_admission_established": False, "scope": "SUPPLIED_AFFINE_MATRIX_ONLY"
              if op == "AFFINE" else "CONDITIONAL_COUNT_ARITHMETIC_ONLY"}
    if op == "COUNT":
        require(len(lines) == 6 and lines[0] == "STATUS CONDITIONAL_ARITHMETIC",
                "wrong COUNT result structure")
        b, epsilon, sigma, M = request[1]
        delta = min(epsilon, sigma / (2 * (M + 1)))
        bound = 2 * (1 + delta) / (b * delta)
        ceiling = (bound.numerator + bound.denominator - 1) // bound.denominator
        require(lines[1] == "DELTA " + qtext(delta), "COUNT delta mismatch")
        require(lines[2] == "BOUND " + qtext(bound), "COUNT bound mismatch")
        require(lines[3] == f"CEILING {ceiling}", "COUNT ceiling mismatch")
        require(lines[4] == "GATE UNKNOWN_SOURCE_PROVIDER", "missing original-source gate")
        require(exit_code is None or exit_code == 2, "conditional count incorrectly promoted exit status")
        return common | {"status": "CONDITIONAL_ARITHMETIC", "delta": qtext(delta),
                         "bound": qtext(bound), "ceiling": ceiling}
    _, n, rows, cap = request
    if lines[0] == "STATUS SAT":
        require(len(lines) == 4 and (exit_code is None or exit_code == 0), "wrong SAT structure/status")
        witness = list_payload(lines[1], "WITNESS", n)
        lhs = list_payload(lines[2], "EVAL", len(rows))
        check_witness(rows, witness, lhs)
        return common | {"status": "SAT", "certificate_valid": True,
                         "witness": list(map(qtext, witness)), "evaluations": list(map(qtext, lhs))}
    if lines[0] == "STATUS UNSAT":
        require(len(lines) == 5 and (exit_code is None or exit_code == 0), "wrong UNSAT structure/status")
        weights = list_payload(lines[1], "MULTIPLIERS", len(rows))
        bound_line = lines[2].split(" ")
        require(len(bound_line) == 2 and bound_line[0] == "BOUND", "bad exclusion bound framing")
        require(lines[3] in ("STRICT 0", "STRICT 1"), "bad exclusion strictness framing")
        aggregate = qparse(bound_line[1])
        strict = lines[3] == "STRICT 1"
        check_exclusion(n, rows, weights, aggregate, strict)
        return common | {"status": "UNSAT", "certificate_valid": True,
                         "multipliers": list(map(qtext, weights)), "bound": qtext(aggregate), "strict": strict}
    if lines[0] == "STATUS UNKNOWN":
        require(len(lines) == 3 and (exit_code is None or exit_code == 2), "wrong UNKNOWN structure/status")
        fields = lines[1].split(" ")
        require(len(fields) == 4 and fields[0] == "LIMIT", "bad projection limit framing")
        dimension, required, returned_cap = map(nparse, fields[1:])
        require(0 < dimension <= n and returned_cap == cap and required > cap,
                "inconsistent projection limit metadata")
        return common | {"status": "UNKNOWN", "reason": "PROJECTION_LIMIT",
                         "dimension": dimension, "required_rows": required, "cap": cap}
    raise ValueError("unrecognized result status")


def check_response(raw_request, raw_result, exit_code):
    return verify_certificate(raw_request, raw_result, exit_code)["status"]


def read_bounded(path, cap):
    with path.open("rb") as stream:
        raw = stream.read(cap + 1)
    require(len(raw) <= cap, "file exceeds byte cap")
    return raw


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", required=True, type=Path)
    parser.add_argument("--certificate", required=True, type=Path)
    parser.add_argument("--exit-code", type=int)
    args = parser.parse_args()
    raw_request = read_bounded(args.request, MAX_REQUEST_BYTES)
    raw_certificate = read_bounded(args.certificate, MAX_CERTIFICATE_BYTES)
    checked = verify_certificate(raw_request, raw_certificate, args.exit_code)
    print(json.dumps(checked, sort_keys=True))
    return 0 if checked["certificate_valid"] else 1 if checked["status"] == "REFUSED" else 2


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, UnicodeError, OSError) as error:
        print(json.dumps({"result_valid": False, "certificate_valid": False, "error": str(error)}, sort_keys=True))
        sys.exit(1)
