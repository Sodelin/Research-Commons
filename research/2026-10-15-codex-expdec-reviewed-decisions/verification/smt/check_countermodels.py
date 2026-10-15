#!/usr/bin/env python3
"""Replay retained rational SAT witnesses without importing or calling Z3."""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(text):
    tokens = re.findall(r"\(|\)|[^\s()]+", text)
    position = 0

    def expression():
        nonlocal position
        if position >= len(tokens):
            raise ValueError("truncated expression")
        token = tokens[position]
        position += 1
        if token == "(":
            values = []
            while position < len(tokens) and tokens[position] != ")":
                values.append(expression())
            if position >= len(tokens):
                raise ValueError("missing closing parenthesis")
            position += 1
            return values
        if token == ")":
            raise ValueError("unexpected closing parenthesis")
        return token

    result = expression()
    if position != len(tokens):
        raise ValueError("unexpected trailing output")
    return result


def rational(value):
    if isinstance(value, str):
        return Fraction(value)
    if len(value) == 2 and value[0] == "-":
        return -rational(value[1])
    if len(value) == 3 and value[0] == "/":
        return rational(value[1]) / rational(value[2])
    raise ValueError("refused non-rational model value")


def validate(identifier, values):
    f = Fraction
    if identifier == "04-constant-shift-key":
        x, q0, q1 = (values[k] for k in ("x", "Q0", "Q1"))
        return x == 0 and q0 == x*x and q1 == x*x+1 and q0 != q1
    if identifier == "06-refitted-parameters":
        t1, t2 = values["theta_1"], values["theta_2"]
        return 0 < t1 < 1 and 0 < t2 < 1 and t1 == f(1, 3) and t2 == f(2, 3) and t1 != t2
    if identifier == "08-relaxed-domain":
        return values["theta"] == 0 and not values["theta"] > 0
    if identifier == "09-single-point-equality":
        a, b, x = (values[k] for k in ("a", "b", "x"))
        return a == 1 and b == 0 and x == 0 and a*x+b == 0 and (a != 0 or b != 0)
    if identifier == "10-open-interval-witness":
        return 0 < values["x"] < 1 and values["x"] != 0
    if identifier == "12-omitted-division-guard":
        n, d, z = (values[k] for k in ("n", "d", "z"))
        return n == d == 0 and z == 42 and z*d == n
    if identifier == "13-surface-versus-open":
        a, b, x, y = (values[k] for k in ("a", "b", "x", "y"))
        return a == 1 and b == -1 and x == y and a*x+b*y == 0 and (a != 0 or b != 0)
    if identifier == "16-delta-slack-counterexample":
        delta, rhat, r = (values[k] for k in ("delta", "rhat", "r"))
        return delta == 1 and rhat == f(-1, 2) and r == f(-3, 4) and abs(rhat-r) <= delta/4 and rhat >= -delta/2 and -delta <= r < 0
    raise ValueError("no independent checker for " + identifier)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    receipt = json.loads(args.receipt.read_text())
    results = []
    for result in receipt["results"]:
        if result["actual"] != "sat":
            continue
        output_path = args.receipt.parent / result["stdout"]
        if digest(output_path) != result["stdout_sha256"]:
            raise ValueError("stdout digest mismatch")
        status, model = output_path.read_text().split("\n", 1)
        if status != "sat":
            raise ValueError("unexpected status")
        assignments = parse(model)
        if any(not isinstance(pair, list) or len(pair) != 2 for pair in assignments):
            raise ValueError("unexpected assignment structure")
        values = {name: rational(value) for name, value in assignments}
        if len(values) != len(assignments):
            raise ValueError("duplicate model variable")
        checked = validate(result["id"], values)
        results.append({"id": result["id"], "valid": checked,
                        "rational_values": {k: str(v) for k, v in values.items()},
                        "solver_stdout_sha256": digest(output_path)})
    document = {"schema": "expdec-independent-rational-countermodel-check-v1",
                "checker_sha256": digest(Path(__file__)),
                "solver_receipt_sha256": digest(args.receipt),
                "uses_z3": False, "arithmetic": "Python stdlib exact Fraction",
                "all_valid": len(results) == 8 and all(r["valid"] for r in results),
                "results": results,
                "scope": "Exact replay of eight supplied rational SAT countermodels only; no independent UNSAT proof-kernel replay."}
    with args.output.open("x") as output:
        json.dump(document, output, indent=2, sort_keys=True)
        output.write("\n")
    print(json.dumps({"models": len(results), "all_valid": document["all_valid"]}))
    if not document["all_valid"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
