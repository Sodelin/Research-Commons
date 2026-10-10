#!/usr/bin/env python3
"""Exact SymPy simplex adjunct, certificate controls and native CLI replay.

This is a distinct rational linear-program algorithm, not a second FM test.
Each unrestricted variable is split into two nonnegative variables. All LT
rows use one positive common slack t, maximized with 0<=t<=1. A finite strict
system is feasible exactly when that maximum is positive. Every returned
simplex assignment is independently checked against its augmented inequalities.
The shared design/parity_harness.py owns Lean/Rust canonical byte parity.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import random
import subprocess
import time


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def wire(value: F) -> str:
    return f"{value.numerator}/{value.denominator}"


def request(n: int, rows: list[tuple[bool, F, list[F]]], cap: int = 4096) -> bytes:
    result = [f"RC1 AFFINE {n} {len(rows)} {cap}\n"]
    for strict, bound, coefficients in rows:
        result.append(" ".join(["LT" if strict else "LE", wire(bound), *map(wire, coefficients)]) + "\n")
    return "".join(result).encode("ascii")


def simplex_status(n: int, rows: list[tuple[bool, F, list[F]]]):
    from sympy import Rational
    from sympy.solvers.simplex import InfeasibleLPError, linprog
    to_sympy = lambda x: Rational(x.numerator, x.denominator)
    # x_i = u_i-v_i with u_i,v_i >= 0; final variable is t >= 0.
    objective = [0] * (2 * n) + [-1]
    matrix = [[to_sympy(a) for a in coefficients] + [-to_sympy(a) for a in coefficients]
              + [int(strict)] for strict, _, coefficients in rows]
    bounds = [to_sympy(bound) for _, bound, _ in rows]
    matrix.append([0] * (2 * n) + [1])
    bounds.append(1)
    try:
        optimum, assignment = linprog(objective, matrix, bounds)
    except InfeasibleLPError:
        return "UNSAT", {"simplex": "INFEASIBLE"}
    point = [F(x) for x in assignment]
    if any(x < 0 for x in point):
        raise ValueError("Simplex returned a negative split variable")
    for coefficients, bound in zip(matrix, bounds):
        if sum((F(a) * x for a, x in zip(coefficients, point)), F(0)) > F(bound):
            raise ValueError("Simplex returned an invalid augmented assignment")
    if F(optimum) != -point[-1]:
        raise ValueError("Simplex optimum disagrees with its assignment")
    strict = any(row[0] for row in rows)
    status = "SAT" if not strict or point[-1] > 0 else "UNSAT"
    return status, {"simplex": "OPTIMUM", "slack": wire(point[-1]),
                    "assignment": [wire(point[i] - point[n + i]) for i in range(n)]}


def fraction_certificate(n, rows, output):
    text = output.decode("ascii")
    body = text.split("END_REQUEST\n", 1)[1].splitlines()
    status = body[0].split()[1]
    if status == "SAT":
        x = list(map(F, body[1].split()[2:]))
        if len(x) != n:
            raise ValueError("wrong witness dimension")
        expected = [sum((a * z for a, z in zip(coefficients, x)), F(0))
                    for _, _, coefficients in rows]
        supplied = list(map(F, body[2].split()[2:]))
        if expected != supplied:
            raise ValueError("wrong row evaluations")
        if not all(lhs < bound if strict else lhs <= bound
                   for lhs, (strict, bound, _) in zip(expected, rows)):
            raise ValueError("invalid exact witness")
    elif status == "UNSAT":
        weights = list(map(F, body[1].split()[2:]))
        if len(weights) != len(rows) or any(w < 0 for w in weights):
            raise ValueError("invalid multiplier shape/sign")
        if any(sum((w * row[2][j] for w, row in zip(weights, rows)), F(0)) != 0 for j in range(n)):
            raise ValueError("multipliers do not annihilate the matrix")
        bound = sum((w * row[1] for w, row in zip(weights, rows)), F(0))
        strict = any(w > 0 and row[0] for w, row in zip(weights, rows))
        if not (bound < 0 or (bound == 0 and strict)):
            raise ValueError("multipliers do not give a contradiction")
        if F(body[2].split()[1]) != bound or int(body[3].split()[1]) != int(strict):
            raise ValueError("incorrect reported contradiction")
    elif status != "UNKNOWN":
        raise ValueError("unexpected status")
    return status


def run(command, input_bytes=None):
    result = subprocess.run(list(map(str, command)), input=input_bytes,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=30, check=False)
    return {"command": list(map(str, command)), "exit_code": result.returncode,
            "stdout": result.stdout, "stderr": result.stderr}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--random-cases", type=int, default=250)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    rust = args.rust.resolve()
    import sympy
    rng = random.Random(20261010)
    records = []
    started = time.monotonic()
    failures = []
    for index in range(args.random_cases):
        n = rng.randrange(4)
        rows = [(bool(rng.randrange(2)), F(rng.randrange(-3, 4), rng.randrange(1, 5)),
                 [F(rng.randrange(-3, 4), rng.randrange(1, 5)) for _ in range(n)])
                for _ in range(rng.randrange(9))]
        data = request(n, rows)
        child = run([rust], data)
        name = f"case-{index:04d}"
        (args.output / f"{name}.request").write_bytes(data)
        (args.output / f"{name}.stdout").write_bytes(child["stdout"])
        (args.output / f"{name}.stderr").write_bytes(child["stderr"])
        record = {"id": name, "request_sha256": sha(data), "stdout_sha256": sha(child["stdout"]),
                  "stderr_sha256": sha(child["stderr"]), "exit_code": child["exit_code"]}
        try:
            actual = fraction_certificate(n, rows, child["stdout"])
            record["rust_status"] = actual
            record["certificate_independently_checked"] = actual in ("SAT", "UNSAT")
            expected, detail = simplex_status(n, rows)
            record.update(oracle_status=expected, oracle=detail)
            record["pass"] = actual == "UNKNOWN" or actual == expected
            if not record["pass"]:
                failures.append(name)
        except Exception as error:
            record.update(pass_=False, error_type=type(error).__name__, error=str(error))
            failures.append(name)
        records.append(record)

    # File/stdin equivalence, fresh output preservation and independent checker
    # rejection of boundary, other-request, false-evaluation and Farkas mutations.
    control_dir = args.output / "controls"
    control_dir.mkdir()
    sat_request = request(1, [(True, F(0), [F(-1)]), (True, F(1), [F(1)])], 1)
    unsat_request = request(1, [(True, F(0), [F(-1)]), (False, F(0), [F(1)])], 1)
    sat_path, unsat_path = control_dir / "sat.request", control_dir / "unsat.request"
    sat_path.write_bytes(sat_request)
    unsat_path.write_bytes(unsat_request)
    certificate_path = control_dir / "sat.certificate"
    solve = run([rust, "solve", sat_path, "--output", certificate_path])
    stdin = run([rust], sat_request)
    check = run([rust, "check", sat_path, certificate_path])
    before = certificate_path.read_bytes()
    preserved = run([rust, "solve", unsat_path, "--output", certificate_path])
    cli = [{"id": "file_stdin_output_identity", "pass": solve["exit_code"] == 0
            and solve["stdout"] == stdin["stdout"] == before},
           {"id": "native_independent_checker", "pass": check["exit_code"] == 0
            and check["stdout"] == b"RC1 CHECK ACCEPT\n"},
           {"id": "fresh_output_preserved", "pass": preserved["exit_code"] == 1
            and certificate_path.read_bytes() == before}]
    mutations = {
        "other_request": (unsat_path, before),
        "open_endpoint": (sat_path, before.replace(b"WITNESS 1 1/2", b"WITNESS 1 0/1")),
        "false_evaluation": (sat_path, before.replace(b"EVAL 2 -1/2 1/2", b"EVAL 2 0/1 1/2")),
        "negative_multiplier": (unsat_path, run([rust], unsat_request)["stdout"].replace(
            b"MULTIPLIERS 2 1/1 1/1", b"MULTIPLIERS 2 -1/1 -1/1")),
        "zero_multiplier_strict": (unsat_path, run([rust], unsat_request)["stdout"].replace(
            b"MULTIPLIERS 2 1/1 1/1", b"MULTIPLIERS 2 0/1 0/1")),
    }
    for name, (original, mutation) in mutations.items():
        path = control_dir / f"{name}.certificate"
        path.write_bytes(mutation)
        child = run([rust, "check", original, path])
        cli.append({"id": name, "pass": child["exit_code"] == 1
                    and child["stdout"] == b"RC1 CHECK REJECT\n"})
        (control_dir / f"{name}.stdout").write_bytes(child["stdout"])
        (control_dir / f"{name}.stderr").write_bytes(child["stderr"])
    summary = {"schema": "rust_exact_simplex_oracle_v1", "status": "PASS" if not failures
               and all(c["pass"] for c in cli) else "FAILED", "seed": 20261010,
               "rust_binary": str(rust), "rust_binary_sha256": sha(rust.read_bytes()),
               "oracle": f"SymPy {sympy.__version__} exact simplex, split free variables, strict slack",
               "random_cases": len(records), "oracle_failures": failures,
               "certificate_checks": sum(r.get("certificate_independently_checked", False) for r in records),
               "unknown_cases": sum(r.get("rust_status") == "UNKNOWN" for r in records),
               "cases": records, "cli_controls": cli, "wall_seconds": time.monotonic() - started,
               "limits": "Finite execution evidence only; no universal arithmetic proof or biological admission."}
    (args.output / "RESULT.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": summary["status"], "random_cases": len(records),
                      "oracle_failures": failures, "cli_controls": len(cli)}))
    raise SystemExit(0 if summary["status"] == "PASS" else 1)


if __name__ == "__main__":
    main()
