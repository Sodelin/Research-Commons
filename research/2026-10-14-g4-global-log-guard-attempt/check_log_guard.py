"""Exact controls for the all-order log-diagonal guard obstruction.

New, isolated contributor arithmetic. This is not a G4 master solver,
not a Lean/Rust build, and not independent review of the hand proof.
Run: python check_log_guard.py --output ARITHMETIC-RECEIPT.json
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from math import comb, factorial
import json
from pathlib import Path


def lam(n: int) -> int:
    return n * (n - 1) // 2


def log_series(b: list[F], order: int) -> list[F]:
    if len(b) < order + 1 or b[0] != 1:
        raise ValueError("A sufficient series with constant coefficient 1 is required")
    out = [F(0)] * (order + 1)
    for j in range(1, order + 1):
        out[j] = b[j] - sum((k * out[k] * b[j-k] for k in range(1, j)), F(0)) / j
    return out


def source_series(n: int, order: int, rho: F, z: F) -> list[F]:
    """Direct polynomial B(rho, 1-z*e, e) no-merger expansion."""
    out = [F(0)] * (order + 1)
    for k in range(min(n, order) + 1):
        used = lam(n-k)
        factor = F(comb(n, k)) * rho ** lam(k)
        for j in range(order-k+1):
            out[k+j] += factor * sum((
                F(comb(n-k, h)) * (-1)**h * F(comb(used, j-h)) * (-z)**(j-h)
                for h in range(max(0, j-used), min(n-k, j)+1)
            ), F(0))
    return out


def leading_coefficient(r: int, rho: F, z: F) -> F:
    """[u^r] log A_rho(u exp(z u)); only finite formal arithmetic."""
    a = [rho ** lam(k) / factorial(k) for k in range(r+1)]
    logs = log_series(a, r)
    return sum((logs[k] * (k*z)**(r-k) / factorial(r-k)
                for k in range(1, r+1)), F(0))


def boundary_coefficient(r: int, z: F) -> F:
    """Independent direct expansion at rho=0; not a physical cell."""
    return sum((F((-1)**(k-1), k) * (k*z)**(r-k) / factorial(r-k)
                for k in range(1, r+1)), F(0))


def z_negative(r: int) -> F:
    return F(r-1) * F(2)**(r-4)


def no_merger(n: int, x: F, y: F, g: F) -> F:
    return sum((F(comb(n, k)) * g**k * (1-g)**(n-k) * x**lam(k) * y**lam(n-k)
                for k in range(n+1)), F(0))


def normalized_integer_product(weights: list[int], x: F, y: F, g: F) -> F:
    """exp(sum_{n>=3} weights[n-3]*(log b_n-lam(n)*log b_2))."""
    b2 = no_merger(2, x, y, g)
    result = F(1)
    for n, weight in enumerate(weights, start=3):
        result *= (no_merger(n, x, y, g) / b2**lam(n))**weight
    return result


def run() -> dict:
    count = 0
    records = []
    # Boundary sign controls supplement, rather than replace, the proof for ALL r.
    for r in range(3, 41):
        z = z_negative(r)
        value = boundary_coefficient(r, z)
        assert value < 0
        assert value == leading_coefficient(r, F(0), z)
        terms = [F(1, k) * (k*z)**(r-k) / factorial(r-k) for k in range(1, r+1)]
        assert terms[1] == 2*terms[0]
        assert all(terms[k+1] <= terms[k]/3 for k in range(1, r-1))
        assert value <= -terms[0]/3
        count += 5
    records.append({"group": "boundary coefficient and decreasing alternating tail", "orders": [3,40], "assertions": 190})

    # Independent direct source expansion checks the degree and top coefficient.
    for r in range(3, 11):
        for z in (z_negative(r), 8*z_negative(r)):
            rho = F(1,100)
            log2 = log_series(source_series(2, r, rho, z), r)
            rows = []
            for n in range(r+3):
                logn = log_series(source_series(n, r, rho, z), r)
                rows.append([logn[j] - lam(n)*log2[j] for j in range(r+1)])
                assert rows[-1][1] == rows[-1][2] == 0
                count += 1
            values = [row[r] for row in rows]
            assert values[:3] == [0,0,0]
            for _ in range(r):
                values = [values[j+1]-values[j] for j in range(len(values)-1)]
            assert len(set(values)) == 1
            assert values[0] == factorial(r)*leading_coefficient(r,rho,z)
            count += 3
    records.append({"group": "direct physical polynomial vs generating-function expansion", "orders": [3,10], "rho": "1/100", "z_choices": "z_r and 8 z_r"})

    for r in range(3, 21):
        minus = leading_coefficient(r, F(1,100), z_negative(r))
        plus = leading_coefficient(r, F(1,100), 8*z_negative(r))
        assert minus < 0 < plus
        count += 1
    records.append({"group": "strict finite rare-arm parameters have both leading signs", "orders": [3,20], "rho": "1/100"})

    examples = []
    for r in range(3, 7):
        # The r-th finite-difference covector kills all lower-degree polynomials.
        weights = [(-1)**(r-n)*comb(r,n) for n in range(3,r+1)]
        for expected, z in ((-1,z_negative(r)),(1,8*z_negative(r))):
            rho = F(1,100)
            found = False
            for power in range(2, 11):
                eps = F(1,10**power) / (1+z)
                y = 1-z*eps
                value = normalized_integer_product(weights,rho,y,eps)
                if (value > 1)-(value < 1) == expected:
                    found = True
                    break
            assert found, "Finite control did not find its exact sign witness"
            b2 = no_merger(2,rho,y,eps)
            c2 = eps*rho + (1-eps)*y
            assert 0 < rho < 1 and 0 < y < 1 and 0 < eps < 1
            assert b2 > F(1,2)
            assert b2-c2 == eps*(1-eps)*(2-rho-y) > 0
            # Two equal positive pads can have product (1/2)/b2.
            assert 0 < F(1,2)/b2 < 1
            count += 5
            examples.append({"order":r,"weights_n3_to_nr":weights,
                             "rho":str(rho),"z":str(z),"epsilon":str(eps),"y":str(y),
                             "exact_product_sign_relative_to_one":expected,
                             "pair_survival_before_padding":str(b2),
                             "common_survival_before_padding":str(c2),
                             "padding_survival_product":str(F(1,2)/b2),
                             "note":"A sign countercontrol, not a full-prefix matching rival"})
    records.append({"group":"actual strict rational cells and target-pair padding", "examples":len(examples)})
    return {"schema":"g4_log_diagonal_guard_controls_v1", "status":"PASS", "assertions_passed":count,
            "arithmetic":"Python standard-library exact integers and Fraction only",
            "groups":records,"actual_source_examples":examples,
            "universal_statement":"hand proof; finite controls are not its quantifier justification",
            "full_legal_prefix_equality":False,"g4_master_closed":False,
            "independently_reviewed":False,"lean_or_rust_executed":False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    print(json.dumps({k:result[k] for k in ("status","assertions_passed","g4_master_closed","lean_or_rust_executed")},sort_keys=True))
