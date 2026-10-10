#!/usr/bin/env python3
"""Invoke two RC1 executables and independently check original-row certificates.

This harness does not prove the Rust implementation or source admission. SAT
and UNSAT are checked directly against the input matrix using Fraction; the
checker does not call either production Fourier--Motzkin implementation.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
DESIGN = Path(__file__).resolve().parent
Q_TOKEN = re.compile(r"(?:0|[1-9][0-9]*|-[1-9][0-9]*)/[1-9][0-9]*\Z")
N_TOKEN = re.compile(r"(?:0|[1-9][0-9]*)\Z")
BIT_BOUND = 1 << 256


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


@dataclass(frozen=True)
class Case:
    name: str
    request: bytes
    expected: str | None = None
    source_scope: str = "affine matrix only"


def matrix_request(n, rows, cap=4096):
    lines = [f"RC1 AFFINE {n} {len(rows)} {cap}"]
    for strict, bound, coeff in rows:
        require(len(coeff) == n, "fixture dimension mismatch")
        tokens = ["LT" if strict else "LE", qtext(bound)]
        tokens.extend(qtext(a) for a in coeff)
        lines.append(" ".join(tokens))
    return ("\n".join(lines) + "\n").encode("ascii")


def count_request(b, epsilon, sigma, M):
    return ("RC1 COUNT " + " ".join(map(qtext, (b, epsilon, sigma, M))) + "\n").encode()


def parse_request(raw):
    require(len(raw) <= 65536, "input exceeds byte cap")
    text = raw.decode("ascii")
    require(text.endswith("\n"), "missing final newline")
    lines = text[:-1].split("\n")
    require(all(line and line == " ".join(line.split(" "))
                and all(line.split(" ")) and "\r" not in line and "\t" not in line
                for line in lines), "noncanonical whitespace")
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


def check_unknown_projection(n, rows, cap, dimension, required):
    """Check the specific resource stopping claim, not an infeasibility claim."""
    current = rows
    for d in range(n, 0, -1):
        zeros = [r for r in current if r.coeff[-1] == 0]
        pos = [r for r in current if r.coeff[-1] > 0]
        neg = [r for r in current if r.coeff[-1] < 0]
        need = len(zeros) + len(pos) * len(neg)
        if need > cap:
            require(dimension == d and required == need, "wrong projection stop metadata")
            return
        projected = [Row(r.strict, r.bound, r.coeff[:-1]) for r in zeros]
        for p in pos:
            for m in neg:
                ap, am = p.coeff[-1], m.coeff[-1]
                projected.append(Row(m.strict or p.strict, -am * p.bound + ap * m.bound,
                                     tuple(-am * a + ap * b
                                           for a, b in zip(p.coeff[:-1], m.coeff[:-1]))))
        current = tuple(projected)
    raise ValueError("UNKNOWN issued without projection exhaustion")


def check_response(raw_request, raw_result, exit_code):
    try:
        request = parse_request(raw_request)
    except (ValueError, UnicodeError, OverflowError):
        require(exit_code == 1 and raw_result == b"RC1 ERROR INVALID_REQUEST\n",
                "invalid input did not produce canonical refusal")
        return "REFUSED"
    op = request[0]
    prefix = f"RC1 RESULT {op}\nBEGIN_REQUEST\n".encode() + raw_request + b"END_REQUEST\n"
    require(raw_result.startswith(prefix), "result changed/omitted complete request bytes")
    payload = raw_result[len(prefix):].decode("ascii")
    require(payload.endswith("\n"), "result missing final newline")
    lines = payload[:-1].split("\n")
    require(lines[-1:] == ["END"], "result lacks exact end framing")
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
        require(exit_code == 2, "conditional count incorrectly promoted exit status")
        return "CONDITIONAL_ARITHMETIC"
    _, n, rows, cap = request
    require(lines, "empty AFFINE payload")
    if lines[0] == "STATUS SAT":
        require(len(lines) == 4 and exit_code == 0, "wrong SAT structure/status")
        witness = list_payload(lines[1], "WITNESS", n)
        lhs = list_payload(lines[2], "EVAL", len(rows))
        check_witness(rows, witness, lhs)
        return "SAT"
    if lines[0] == "STATUS UNSAT":
        require(len(lines) == 5 and exit_code == 0, "wrong UNSAT structure/status")
        weights = list_payload(lines[1], "MULTIPLIERS", len(rows))
        bound_line = lines[2].split(" ")
        require(len(bound_line) == 2 and bound_line[0] == "BOUND", "bad exclusion bound framing")
        require(lines[3] in ("STRICT 0", "STRICT 1"), "bad exclusion strictness framing")
        check_exclusion(n, rows, weights, qparse(bound_line[1]), lines[3] == "STRICT 1")
        return "UNSAT"
    if lines[0] == "STATUS UNKNOWN":
        require(len(lines) == 3 and exit_code == 2, "wrong UNKNOWN structure/status")
        fields = lines[1].split(" ")
        require(len(fields) == 4 and fields[0] == "LIMIT", "bad projection limit framing")
        dimension, required, returned_cap = map(nparse, fields[1:])
        require(returned_cap == cap, "projection limit changed request cap")
        check_unknown_projection(n, rows, cap, dimension, required)
        return "UNKNOWN"
    raise ValueError("unrecognized result status")


def fixed_cases():
    cases = []

    def add(name, n, rows, expected=None, cap=4096, scope="affine matrix only"):
        cases.append(Case(name, matrix_request(n, rows, cap), expected, scope))

    add("zero_dimension_empty", 0, [], "SAT")
    add("zero_dimension_weak_zero", 0, [(False, 0, [])], "SAT")
    add("zero_dimension_strict_zero", 0, [(True, 0, [])], "UNSAT")
    add("zero_dimension_negative", 0, [(False, -1, [])], "UNSAT")
    add("empty_bank", 4, [], "SAT", cap=0)
    add("weak_singleton", 1, [(False, 1, [1]), (False, -1, [-1])], "SAT")
    add("strict_singleton", 1, [(True, 1, [1]), (False, -1, [-1])], "UNSAT")
    add("tied_strict_upper", 1, [(False, 1, [1]), (True, 1, [2]), (False, -Fraction(1, 2), [-1])], "UNSAT")
    add("opposite_sign_yes", 2, [(True, 1, [1, 1]), (False, 0, [-1, -1])], "SAT")
    add("opposite_sign_no", 2, [(True, 0, [1, 1]), (False, 0, [-1, -1])], "UNSAT")
    add("lower_only", 2, [(True, 3, [-1, -1])], "SAT")
    add("upper_only", 2, [(True, -3, [1, 1])], "SAT")
    add("repeated_rows", 1, [(False, 2, [1]), (False, 2, [1]), (True, 0, [-1])], "SAT")
    add("projection_limit", 2, [(False, 1, [0, 1]), (False, 0, [0, -1])], "UNKNOWN", cap=0)
    add("later_projection_limit", 2, [(False, 1, [1, 0]), (False, 0, [-1, 0])], "UNKNOWN", cap=1)
    big = (1 << 255) - 19
    add("large_denominator", 1, [(True, Fraction(1, big), [1]), (True, 0, [-1])], "SAT")
    # Explicit original two-tip source bank: root/tip ages, each edge inverse
    # rate, ancestral inverse rate. Its relationship to compileCell is hand
    # derived until a concrete Lean compiler-output equality is checked.
    chart = [(True, 0, [-1, 1, 0, 0, 0, 0]), (True, 0, [-1, 0, 1, 0, 0, 0]),
             (False, 0, [0, 1, 0, 0, 0, 0]), (False, 0, [0, -1, 0, 0, 0, 0]),
             (False, 0, [0, 0, 1, 0, 0, 0]), (False, 0, [0, 0, -1, 0, 0, 0]),
             (True, 0, [0, 0, 0, -1, 0, 0]), (True, 0, [0, 0, 0, 0, -1, 0]),
             (True, 0, [0, 0, 0, 0, 0, -1]),
             (False, 0, [-1, 1, 0, 1, 0, 0]), (False, 0, [1, -1, 0, -4, 0, 0]),
             (False, 0, [-1, 0, 1, 0, 1, 0]), (False, 0, [1, 0, -1, 0, -4, 0])]
    add("two_tip_natural_cell", 6, chart, "SAT", scope="hand-derived ordinary two-tip source chart")
    add("two_tip_natural_cell_contradiction", 6,
        chart + [(False, 0, [1, 0, 0, 0, 0, 0])], "UNSAT",
        scope="one hand-derived ordinary two-tip chart only")
    for name, args in [("conditional_count_example", (Fraction(1, 4), Fraction(1, 2), 1, 0)),
                       ("conditional_count_67", (Fraction(3, 4), Fraction(1, 3), Fraction(1, 4), 2)),
                       ("conditional_count_M_zero", (2, Fraction(1, 7), 2, 0))]:
        cases.append(Case(name, count_request(*args), "CONDITIONAL_ARITHMETIC", "conditional count arithmetic only"))
    valid = matrix_request(1, [(False, 1, [1])])
    bad = {
        "bad_missing_lf": valid[:-1],
        "bad_extra_lf": valid + b"\n",
        "bad_crlf": valid.replace(b"\n", b"\r\n"),
        "bad_tab": valid.replace(b" ", b"\t", 1),
        "bad_double_space": valid.replace(b" ", b"  ", 1),
        "bad_negative_zero": valid.replace(b"1/1", b"-0/1", 1),
        "bad_unreduced": valid.replace(b"1/1", b"2/2", 1),
        "bad_leading_zero": valid.replace(b"1/1", b"01/1", 1),
        "bad_negative_denominator": valid.replace(b"1/1", b"1/-1", 1),
        "bad_no_denominator": valid.replace(b"1/1", b"1", 1),
        "bad_float": valid.replace(b"1/1", b"1.0", 1),
        "bad_nan": valid.replace(b"1/1", b"NaN", 1),
        "bad_infinite": valid.replace(b"1/1", b"Infinity", 1),
        "bad_zero_denominator": valid.replace(b"1/1", b"1/0", 1),
        "bad_wrong_dimension": b"RC1 AFFINE 9 0 4096\n",
        "bad_wrong_rowcount": valid.replace(b"AFFINE 1 1", b"AFFINE 1 2"),
        "bad_extra_field": valid.replace(b"LE", b"LE UNKNOWN_FIELD"),
        "bad_multiple_requests": valid + valid,
        "bad_json_duplicate_keys": b'{"n":1,"n":2}\n',
        "bad_json_unknown_field": b'{"unknown":true}\n',
        "bad_non_ascii": valid + b"\xff",
        "bad_bit_limit": b"RC1 COUNT " + str(1 << 256).encode() + b"/1 1/1 1/1 0/1\n",
        "bad_oversized": b"X" * 65537,
        "bad_zero_b": count_request(0, 1, 1, 0),
        "bad_negative_M": count_request(1, 1, 1, -1),
    }
    cases.extend(Case(name, raw, "REFUSED", "transport refusal") for name, raw in bad.items())
    return cases


def randomized_cases(seed, count):
    rng = random.Random(seed)
    cases = []
    for index in range(count):
        n = rng.randrange(0, 5)
        m = rng.randrange(0, 9)
        rows = []
        # Half the systems have a constructed shared solution, although a
        # small projection cap may still conservatively return UNKNOWN.
        known = tuple(Fraction(rng.randrange(-3, 4), rng.randrange(1, 5)) for _ in range(n))
        for _ in range(m):
            coeff = tuple(Fraction(rng.randrange(-3, 4), rng.randrange(1, 5)) for _ in range(n))
            strict = bool(rng.getrandbits(1))
            if index % 2 == 0:
                bound = dot(coeff, known) + Fraction(rng.randrange(1 if strict else 0, 5), rng.randrange(1, 5))
            else:
                bound = Fraction(rng.randrange(-3, 4), rng.randrange(1, 5))
            rows.append((strict, bound, coeff))
        cap = rng.choice((0, 1, 8, 64, 4096))
        expected = "SAT" if index % 2 == 0 and n == 0 else None
        cases.append(Case(f"random_{index:04d}", matrix_request(n, rows, cap), expected))
        if index < min(count, 20):
            reordered = list(reversed(rows))
            cases.append(Case(f"reordered_{index:04d}", matrix_request(n, reordered, cap)))
            if m < 64 and rows:
                cases.append(Case(f"duplicated_{index:04d}", matrix_request(n, rows + [rows[0]], cap)))
    return cases


def verifier_adversarial_checks():
    """The checker itself must reject valid-looking false evidence."""
    rows = (Row(True, Fraction(0), (Fraction(1),)), Row(False, Fraction(0), (Fraction(-1),)))
    good = (Fraction(1), Fraction(1))
    check_exclusion(1, rows, good, Fraction(0), True)
    attacks = [lambda: check_exclusion(1, rows, good, Fraction(0), False),
               lambda: check_exclusion(1, rows, (Fraction(-1), Fraction(-1)), Fraction(0), True),
               lambda: check_exclusion(1, rows, (Fraction(1), Fraction(0)), Fraction(0), True),
               lambda: check_exclusion(1, rows, good, Fraction(-1), True),
               lambda: check_witness(rows, (Fraction(0),)),
               lambda: check_witness((Row(False, Fraction(2), (Fraction(1),)),),
                                     (Fraction(1),), (Fraction(2),))]
    rejected = 0
    for attack in attacks:
        try:
            attack()
        except ValueError:
            rejected += 1
    require(rejected == len(attacks), "independent checker accepted an adversarial certificate")
    return {"valid_exclusion_checked": 1, "forged_certificates_rejected": rejected}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def execute(binary, request, timeout, extra_args=()):
    start = time.monotonic()
    try:
        proc = subprocess.run([str(binary), *extra_args], input=request, capture_output=True, timeout=timeout)
        return {"exit_code": proc.returncode, "stdout": proc.stdout, "stderr": proc.stderr,
                "elapsed_seconds": time.monotonic() - start, "process_started": True}
    except subprocess.TimeoutExpired as e:
        return {"exit_code": None, "stdout": e.stdout or b"", "stderr": e.stderr or b"",
                "elapsed_seconds": time.monotonic() - start, "process_started": True,
                "execution_failure": "wall timeout"}
    except OSError as e:
        return {"exit_code": None, "stdout": b"", "stderr": str(e).encode(),
                "elapsed_seconds": time.monotonic() - start, "process_started": False,
                "execution_failure": type(e).__name__}


def run(args):
    output = args.output.resolve()
    require(not output.exists(), "output path already exists; use a fresh evidence directory")
    lean, rust = args.lean_bin.resolve(), args.rust_bin.resolve()
    require(lean.is_file() and rust.is_file(), "both executable files must exist")
    cases = fixed_cases() + randomized_cases(args.seed, args.random_cases)
    if args.requests_dir:
        for path in sorted(args.requests_dir.resolve().glob("*.req")):
            cases.append(Case("external_" + path.stem, path.read_bytes()))
    output.mkdir(parents=True)
    case_dir = output / "cases"
    case_dir.mkdir()
    records = []
    passed = 0
    adversarial = verifier_adversarial_checks()
    for index, case in enumerate(cases):
        prefix = f"{index:04d}-{case.name}"
        (case_dir / (prefix + ".req")).write_bytes(case.request)
        runs = {name: execute(binary, case.request, args.timeout, command_args)
                for name, binary, command_args in (("lean", lean, args.lean_arg),
                                                    ("rust", rust, args.rust_arg))}
        for name, value in runs.items():
            for stream in ("stdout", "stderr"):
                (case_dir / f"{prefix}.{name}.{stream}").write_bytes(value[stream])
        errors, statuses = [], {}
        for name, value in runs.items():
            if "execution_failure" in value or value["exit_code"] not in (0, 1, 2):
                errors.append(name + " execution failure: " + value.get("execution_failure", str(value["exit_code"])))
                continue
            try:
                statuses[name] = check_response(case.request, value["stdout"], value["exit_code"])
            except (ValueError, UnicodeError, OverflowError) as e:
                errors.append(name + " independent verification: " + str(e))
        if runs["lean"]["stdout"] != runs["rust"]["stdout"]:
            errors.append("Lean/Rust output bytes differ")
        if runs["lean"]["exit_code"] != runs["rust"]["exit_code"]:
            errors.append("Lean/Rust exit codes differ")
        if case.expected and any(status != case.expected for status in statuses.values()):
            errors.append("result differs from fixture expectation " + case.expected)
        record = {"name": case.name, "scope": case.source_scope, "expected": case.expected,
                  "request_sha256": digest(case.request), "status": statuses,
                  "pass": not errors, "errors": errors,
                  "runs": {name: {k: v for k, v in value.items() if k not in ("stdout", "stderr")}
                            | {"stdout_sha256": digest(value["stdout"]), "stderr_sha256": digest(value["stderr"])}
                           for name, value in runs.items()}}
        records.append(record)
        if not errors:
            passed += 1
        else:
            print(case.name + ": " + "; ".join(errors), file=sys.stderr, flush=True)
    identity = {"harness": {"path": str(Path(__file__).resolve()), "sha256": digest(Path(__file__).read_bytes())},
                "contract": {"path": str(DESIGN / "CONTRACT.md"), "sha256": digest((DESIGN / "CONTRACT.md").read_bytes())},
                "executables": {name: {"path": str(path), "sha256": digest(path.read_bytes()),
                                       "arguments": command_args}
                                for name, path, command_args in (("lean", lean, args.lean_arg),
                                                                 ("rust", rust, args.rust_arg))}}
    receipt = {"claim": "FINITE_LEAN_RUST_EXECUTION_PARITY_AND_ORIGINAL_ROW_CERTIFICATE_CHECKING",
               "source_admission_claim": False, "general_G3_G4_claim": False,
               "universal_Rust_Lean_equivalence_claim": False,
               "executed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "seed": args.seed, "random_cases": args.random_cases,
               "cases_total": len(records), "cases_passed": passed,
               "pass": passed == len(records), "independent_checker_controls": adversarial,
               "identities": identity, "cases": records}
    (output / "PARITY-RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": receipt["pass"], "cases_passed": passed, "cases_total": len(records),
                      "receipt": str(output / "PARITY-RECEIPT.json")}))
    return 0 if receipt["pass"] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--rust-bin", type=Path)
    parser.add_argument("--lean-arg", action="append", default=[])
    parser.add_argument("--rust-arg", action="append", default=[])
    parser.add_argument("--output", type=Path)
    parser.add_argument("--requests-dir", type=Path)
    parser.add_argument("--random-cases", type=int, default=200)
    parser.add_argument("--seed", type=int, default=20261010)
    parser.add_argument("--timeout", type=float, default=15)
    parser.add_argument("--write-fixtures", type=Path)
    parser.add_argument("--check-verifier", action="store_true")
    args = parser.parse_args()
    if args.check_verifier:
        print(json.dumps(verifier_adversarial_checks(), sort_keys=True))
        return 0
    if args.write_fixtures:
        require(not args.write_fixtures.exists(), "fixture output path exists")
        args.write_fixtures.mkdir(parents=True)
        metadata = []
        for case in fixed_cases():
            path = args.write_fixtures / (case.name + ".req")
            path.write_bytes(case.request)
            metadata.append({"name": case.name, "expected": case.expected, "scope": case.source_scope,
                             "request_sha256": digest(case.request)})
        (args.write_fixtures / "INDEX.json").write_text(json.dumps(metadata, indent=2) + "\n")
        print(json.dumps({"fixtures_written": len(metadata), "output": str(args.write_fixtures.resolve())}))
        return 0
    require(args.lean_bin and args.rust_bin and args.output,
            "--lean-bin, --rust-bin and --output are required for actual parity")
    require(0 <= args.random_cases <= 10000 and args.timeout > 0, "invalid harness resource bounds")
    return run(args)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
