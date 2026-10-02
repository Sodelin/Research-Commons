"""Exact one-source rank witness for the enhanced retained-factor criterion.

This verifies finite rational algebra, not the analytic IFT/source transfer.
The prior accepted paired normal and residue rank are preserved as dependencies.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json


def determinant(matrix):
    a = [list(row) for row in matrix]
    answer = Q(1)
    for k in range(len(a)):
        pivot = next((i for i in range(k, len(a)) if a[i][k]), None)
        if pivot is None:
            return Q(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            answer = -answer
        value = a[k][k]
        answer *= value
        for i in range(k + 1, len(a)):
            scale = a[i][k] / value
            for j in range(k + 1, len(a)):
                a[i][j] -= scale * a[k][j]
            a[i][k] = Q(0)
    return answer


def main():
    root = Path(__file__).resolve().parent
    normal_path = root / "paired-normal-algebra.json"
    data = json.loads(normal_path.read_text())["F1"]
    exponents = data["exponents"]
    c = list(map(Q, data["c"]))
    r = p = q = Q(1, 2)
    columns = [
        list(map(Q, exponents)),
        [sum((r**j for j in range(lam)), Q(0)) for lam in exponents],
        [sum((j*r**(j-1) for j in range(1, lam)), Q(0)) for lam in exponents],
        [1-r**(2*lam) for lam in exponents],
        [-lam*r**(2*(lam-1)) for lam in exponents],
    ]
    # The final residue column differentiates at the independent node r^2.
    assert all(sum((ci*value for ci, value in zip(c, column)), Q(0)) == 0
               for column in columns)
    hp = [(1-q**lam)/(1-p+p*q**lam) for lam in exponents]
    hq = [-p*lam*q**(lam-1)/(1-p+p*q**lam) for lam in exponents]
    cp = sum((ci*value for ci, value in zip(c, hp)), Q(0))
    cq = sum((ci*value for ci, value in zip(c, hq)), Q(0))
    matrix = list(map(list, zip(*(columns + [hp]))))
    det = determinant(matrix)
    assert cp != 0 and det != 0
    record = {
        "status": "PASS exact rational augmented-rank witness",
        "cap": 7,
        "residue_node": str(r),
        "retained_probability": str(p),
        "retained_ratio": str(q),
        "exponents": exponents,
        "normal_source_sha256": hashlib.sha256(normal_path.read_bytes()).hexdigest(),
        "normal_annihilates_five_residue_columns": True,
        "c_dot_Hp": str(cp),
        "c_dot_Hq": str(cq),
        "augmented_six_by_six_determinant": str(det),
        "matrix_rows": [[str(value) for value in row] for row in matrix],
        "scope": "Finite rational rank only. Enhanced analytic IFT, normal-form interior and actual-source transfer remain hand obligations; no finite source witness is extracted.",
    }
    (root / "enhanced-retained-rank-check.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: record[key] for key in ["status", "c_dot_Hp", "c_dot_Hq", "augmented_six_by_six_determinant"]}))


if __name__ == "__main__":
    main()
