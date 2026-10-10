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
import subprocess
import sys
import time

from certificate_check import (
    Row, require, qtext, qparse, nparse, parse_request, dot, holds,
    check_witness, check_exclusion, list_payload,
    check_response as validate_response,
)

ROOT = Path(__file__).resolve().parents[3]
DESIGN = Path(__file__).resolve().parent
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
    if raw_request.startswith(b"RC1 CHART "):
        from chart_check import verify_chart_certificate, parse_chart, compile_chart
        checked = verify_chart_certificate(raw_request, raw_result, exit_code)
        if checked["status"] == "UNKNOWN":
            chart = parse_chart(raw_request)
            check_unknown_projection(chart.dimension, compile_chart(chart), chart.cap,
                                     checked["dimension"], checked["required_rows"])
        return checked["status"]
    status = validate_response(raw_request, raw_result, exit_code)
    if status == "UNKNOWN":
        _, n, rows, cap = parse_request(raw_request)
        prefix = b"RC1 RESULT AFFINE\nBEGIN_REQUEST\n" + raw_request + b"END_REQUEST\n"
        line = raw_result[len(prefix):].decode("ascii").splitlines()[1]
        _, dimension, required, _ = line.split(" ")
        check_unknown_projection(n, rows, cap, nparse(dimension), nparse(required))
    return status


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


def chart_verifier_adversarial_checks(responses, output):
    """Challenge compiler identity, shared banks, source gate and certificates."""
    from chart_check import verify_chart_certificate
    require(all(status in responses for status in ("SAT", "UNSAT", "UNKNOWN")),
            "CHART controls require actual conclusive and resource-limited outputs")
    sat_request, sat, sat_exit = responses["SAT"]
    no_request, no, no_exit = responses["UNSAT"]
    unknown_request, unknown, unknown_exit = responses["UNKNOWN"]
    attacks = []

    def attack(name, request, result, exit_code):
        attacks.append((name, request, result, exit_code))

    attack("sat_exit_mismatch", sat_request, sat, 2)
    attack("unsat_exit_mismatch", no_request, no, 2)
    attack("unknown_exit_mismatch", unknown_request, unknown, 0)
    attack("ancestral_bank_alias", sat_request, sat.replace(b"RATE:A", b"RATE:0", 1), sat_exit)
    attack("source_gate_removed", sat_request,
           sat.replace(b"GATE SOURCE_ADMISSION_NOT_ESTABLISHED\n", b"", 1), sat_exit)
    attack("request_echo_substituted", sat_request,
           sat.replace(b"BEGIN_REQUEST\n" + sat_request, b"BEGIN_REQUEST\n" + sat_request.replace(b"ROOT 0", b"ROOT 1"), 1), sat_exit)
    start = sat.index(b"\n", sat.index(b"MATRIX ")) + 1
    stop = sat.index(b"END_MATRIX\n", start)
    rows = sat[start:stop].splitlines(keepends=True)
    swapped = [rows[1], rows[0], *rows[2:]]
    attack("matrix_row_reordered", sat_request, sat[:start] + b"".join(swapped) + sat[stop:], sat_exit)
    duplicated = [rows[0], rows[0], *rows[2:]]
    attack("original_edge_occurrence_collapsed", sat_request, sat[:start] + b"".join(duplicated) + sat[stop:], sat_exit)
    attack("matrix_strictness_changed", sat_request,
           sat[:start] + sat[start:stop].replace(b"LT ", b"LE ", 1) + sat[stop:], sat_exit)
    payload = sat.splitlines(keepends=True)
    bad_witness, bad_eval = list(payload), list(payload)
    for i, line in enumerate(payload):
        if line.startswith(b"WITNESS "):
            tokens = line.decode().split()
            bad_witness[i] = ("WITNESS " + tokens[1] + " 0/1" * int(tokens[1]) + "\n").encode()
        if line.startswith(b"EVAL "):
            tokens = line.decode().split()
            bad_witness[i] = ("EVAL " + tokens[1] + " 0/1" * int(tokens[1]) + "\n").encode()
            tokens[2] = qtext(qparse(tokens[2]) + 1)
            bad_eval[i] = (" ".join(tokens) + "\n").encode()
    attack("zero_bank_with_forged_evaluations", sat_request, b"".join(bad_witness), sat_exit)
    attack("original_row_evaluation_changed", sat_request, b"".join(bad_eval), sat_exit)
    strict_token = b"STRICT 1\n" if b"STRICT 1\n" in no else b"STRICT 0\n"
    flipped = b"STRICT 0\n" if strict_token == b"STRICT 1\n" else b"STRICT 1\n"
    attack("exclusion_strictness_forged", no_request, no.replace(strict_token, flipped, 1), no_exit)
    bad_weights = no.splitlines(keepends=True)
    for i, line in enumerate(bad_weights):
        if line.startswith(b"MULTIPLIERS "):
            tokens = line.decode().split()
            tokens[2] = "-1/1"
            bad_weights[i] = (" ".join(tokens) + "\n").encode()
    attack("negative_exclusion_multiplier", no_request, b"".join(bad_weights), no_exit)
    bad_limit = unknown.splitlines(keepends=True)
    for i, line in enumerate(bad_limit):
        if line.startswith(b"LIMIT "):
            tokens = line.decode().split()
            tokens[1] = "999"
            bad_limit[i] = (" ".join(tokens) + "\n").encode()
    attack("unknown_dimension_forged", unknown_request, b"".join(bad_limit), unknown_exit)
    attack("truncated_chart_certificate", sat_request, sat[:-4], sat_exit)
    output.mkdir()
    records = []
    for name, request, result, exit_code in attacks:
        (output / (name + ".req")).write_bytes(request)
        (output / (name + ".stdout")).write_bytes(result)
        try:
            verify_chart_certificate(request, result, exit_code)
        except (ValueError, UnicodeError) as error:
            records.append({"name": name, "rejected": True, "exit_code": exit_code,
                            "request_sha256": digest(request), "certificate_sha256": digest(result), "reason": str(error)})
        else:
            records.append({"name": name, "rejected": False})
    require(all(record["rejected"] for record in records), "independent CHART checker accepted forged evidence")
    return {"forged_certificates_rejected": len(records), "controls": records}


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
    cases = [] if args.chart_only else fixed_cases() + randomized_cases(args.seed, args.random_cases)
    if args.include_chart or args.chart_only:
        from chart_fixtures import chart_cases
        cases.extend(chart_cases())
    if args.requests_dir:
        for path in sorted(args.requests_dir.resolve().glob("*.req")):
            cases.append(Case("external_" + path.stem, path.read_bytes()))
    output.mkdir(parents=True)
    source_names = ["parity_harness.py", "certificate_check.py", "CONTRACT.md"]
    if args.include_chart or args.chart_only or any(c.request.startswith(b"RC1 CHART ") for c in cases):
        source_names += ["chart_check.py", "chart_fixtures.py", "CHART-CONTRACT.md"]
    source_snapshot = output / "source-snapshot"
    source_snapshot.mkdir()
    source_identities = {}
    for name in source_names:
        raw = (DESIGN / name).read_bytes()
        (source_snapshot / name).write_bytes(raw)
        source_identities[name] = {"path": str(DESIGN / name), "sha256": digest(raw)}
    before_binary_hashes = {name: digest(path.read_bytes()) for name, path in (("lean", lean), ("rust", rust))}
    case_dir = output / "cases"
    case_dir.mkdir()
    records = []
    passed = 0
    adversarial = verifier_adversarial_checks()
    chart_responses = {}
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
        if case.request.startswith(b"RC1 CHART ") and not errors and statuses.get("lean") in ("SAT", "UNSAT", "UNKNOWN"):
            chart_responses.setdefault(statuses["lean"], (case.request, runs["lean"]["stdout"], runs["lean"]["exit_code"]))
        if not errors:
            passed += 1
        else:
            print(case.name + ": " + "; ".join(errors), file=sys.stderr, flush=True)
    if chart_responses:
        adversarial["chart_controls"] = chart_verifier_adversarial_checks(chart_responses, output / "checker-controls")
    after_binary_hashes = {name: digest(path.read_bytes()) for name, path in (("lean", lean), ("rust", rust))}
    identities_stable = before_binary_hashes == after_binary_hashes and all(
        digest((DESIGN / name).read_bytes()) == pinned["sha256"] for name, pinned in source_identities.items())
    identity = {"harness": {"path": str(Path(__file__).resolve()), "sha256": digest(Path(__file__).read_bytes())},
                "contract": {"path": str(DESIGN / "CONTRACT.md"), "sha256": digest((DESIGN / "CONTRACT.md").read_bytes())},
                "source_snapshot": source_identities, "binary_sha256_before": before_binary_hashes,
                "binary_sha256_after": after_binary_hashes, "identities_stable": identities_stable,
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
               "pass": passed == len(records) and identities_stable, "independent_checker_controls": adversarial,
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
    parser.add_argument("--include-chart", action="store_true")
    parser.add_argument("--chart-only", action="store_true")
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
