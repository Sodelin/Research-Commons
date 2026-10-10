#!/usr/bin/env python3
"""Challenge AFFINE decisions with an independent exact graph algorithm.

Difference inequalities x_i-x_j <= b correspond to weighted graph edges.
Strict inequalities carry a negative infinitesimal: (b, -1), compared
lexicographically. Feasibility is equivalent to absence of a negative cycle.
The oracle uses Floyd--Warshall, not Fourier--Motzkin elimination.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
import subprocess
import time


def sha(data):
    return hashlib.sha256(data).hexdigest()


def rational(value):
    return f"{value.numerator}/{value.denominator}"


def feasible(n, constraints):
    distance = [[None] * (n + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        distance[i][i] = (Fraction(0), 0)
    for i, j, bound, strict in constraints:
        edge = (bound, -int(strict))
        current = distance[j][i]
        if current is None or edge < current:
            distance[j][i] = edge
    for k in range(n + 1):
        for i in range(n + 1):
            for j in range(n + 1):
                left, right = distance[i][k], distance[k][j]
                if left is None or right is None:
                    continue
                candidate = (left[0] + right[0], left[1] + right[1])
                old = distance[i][j]
                if old is None or candidate < old:
                    distance[i][j] = candidate
    return all(distance[i][i] >= (Fraction(0), 0) for i in range(n + 1))


def request(n, constraints):
    lines = [f"RC1 AFFINE {n} {len(constraints)} 4096"]
    for i, j, bound, strict in constraints:
        coefficients = [Fraction(0)] * n
        if i:
            coefficients[i - 1] += 1
        if j:
            coefficients[j - 1] -= 1
        row = ["LT" if strict else "LE", rational(bound)]
        row.extend(map(rational, coefficients))
        lines.append(" ".join(row))
    return ("\n".join(lines) + "\n").encode("ascii")


def cases():
    # Deliberate checks of strict zero cycles and fixed-coordinate equality.
    known = [
        (0, [], True),
        (0, [(0, 0, Fraction(0), False)], True),
        (0, [(0, 0, Fraction(0), True)], False),
        (1, [(1, 0, Fraction(0), False), (0, 1, Fraction(0), False)], True),
        (1, [(1, 0, Fraction(0), True), (0, 1, Fraction(0), False)], False),
        (2, [(1, 2, Fraction(1, 7), False), (2, 1, Fraction(-1, 7), True)], False),
        (3, [(1, 2, Fraction(1, 7), True), (2, 3, Fraction(1, 7), False), (3, 1, Fraction(-2, 7), False)], False),
        (3, [(1, 2, Fraction(1, 7), True), (2, 3, Fraction(1, 7), True), (3, 1, Fraction(-1, 7), True)], True),
        (2, [(1, 2, Fraction(1, 2**255 - 19), True)], True),
    ]
    for index, (n, rows, expected) in enumerate(known):
        actual = feasible(n, rows)
        if actual != expected:
            raise ValueError(f"Oracle failed known case {index}")
        yield f"known-{index:03d}", n, rows, expected
    rng = random.Random(20261010)
    for index in range(240):
        n = 1 + index % 3
        rows = [(rng.randrange(n + 1), rng.randrange(n + 1),
                 Fraction(rng.randrange(-4, 5), rng.randrange(1, 8)),
                 bool(rng.randrange(2))) for _ in range(rng.randrange(8))]
        yield f"random-{index:03d}", n, rows, feasible(n, rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--rust", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    binaries = {"lean": args.lean.resolve(strict=True), "rust": args.rust.resolve(strict=True)}
    args.output.mkdir(parents=True, exist_ok=False)
    before = {name: sha(path.read_bytes()) for name, path in binaries.items()}
    summary = []
    for name, n, constraints, expected in cases():
        data = request(n, constraints)
        directory = args.output / name
        directory.mkdir()
        (directory / "REQUEST.rc1").write_bytes(data)
        row = {"case": name, "expected": "SAT" if expected else "UNSAT", "request_sha256": sha(data), "executions": {}}
        results = {}
        for language, path in binaries.items():
            started = time.monotonic()
            process = subprocess.run([str(path)], input=data, capture_output=True, timeout=20)
            (directory / f"{language}.stdout").write_bytes(process.stdout)
            (directory / f"{language}.stderr").write_bytes(process.stderr)
            statuses = [line.removeprefix(b"STATUS ") for line in process.stdout.splitlines() if line.startswith(b"STATUS ")]
            status = statuses[0].decode("ascii") if len(statuses) == 1 else "INVALID_OUTPUT"
            results[language] = process.stdout
            row["executions"][language] = {"returncode": process.returncode, "status": status,
                "elapsed_seconds": time.monotonic() - started,
                "stdout_sha256": sha(process.stdout), "stderr_sha256": sha(process.stderr)}
            if process.returncode != 0 or status != row["expected"]:
                (directory / "FAILURE.json").write_text(json.dumps(row, indent=2) + "\n")
                raise ValueError(f"{name}: {language} disagrees with exact negative-cycle oracle")
        if results["lean"] != results["rust"]:
            raise ValueError(f"{name}: canonical output bytes disagree")
        summary.append(row)
    after = {name: sha(path.read_bytes()) for name, path in binaries.items()}
    if before != after:
        raise ValueError("An executable changed during review")
    receipt = {"status": "INDEPENDENT_DIFFERENCE_CONSTRAINT_REVIEW_PASS",
        "algorithm": "Exact rational/strict-infinitesimal Floyd--Warshall negative-cycle oracle",
        "case_count": len(summary), "source_sha256": sha(Path(__file__).read_bytes()),
        "binaries_sha256": before, "cases": summary,
        "scope": "Finite difference-constraint decisions and cross-language bytes; no general refinement proof or original-source admission."}
    (args.output / "RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": receipt["status"], "cases": len(summary), "receipt": str((args.output / "RECEIPT.json").resolve())}))


if __name__ == "__main__":
    main()
