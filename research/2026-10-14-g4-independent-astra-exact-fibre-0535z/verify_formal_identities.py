"""Exact formal controls only. No source kernels, optimization, Lean or Rust.

Run with Python 3.10+; the standard library suffices. Output is a JSON receipt.
Coefficients are Fractions in a free noncommutative algebra truncated by weight.
"""
from __future__ import annotations
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

CAP = 6
Word = tuple[str, ...]
Key = tuple[int, Word]
Poly = dict[Key, Q]


def clean(p: Poly) -> Poly:
    return {k: v for k, v in p.items() if v and k[0] <= CAP}


def add(*ps: Poly) -> Poly:
    out: Poly = {}
    for p in ps:
        for k, v in p.items():
            out[k] = out.get(k, Q(0)) + v
    return clean(out)


def scale(p: Poly, c: Q | int) -> Poly:
    return clean({k: v * c for k, v in p.items()})


def mul(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for (a, u), x in p.items():
        for (b, v), y in q.items():
            if a + b <= CAP:
                k = (a + b, u + v)
                out[k] = out.get(k, Q(0)) + x * y
    return clean(out)


ONE: Poly = {(0, ()): Q(1)}


def atom(name: str, weight: int) -> Poly:
    if weight <= 0:
        raise ValueError("Positive weight required")
    return {(weight, (name,)): Q(1)}


def exp0(p: Poly) -> Poly:
    if any(k[0] == 0 for k in p):
        raise ValueError("Exponential requires zero constant coefficient")
    out, term = ONE, ONE
    for n in range(1, CAP + 1):
        term = scale(mul(term, p), Q(1, n))
        out = add(out, term)
    return out


def log1(p: Poly) -> Poly:
    if p.get((0, ()), Q(0)) != 1 or any(k[0] == 0 and k[1] for k in p):
        raise ValueError("Logarithm requires unit constant coefficient")
    a = add(p, scale(ONE, -1))
    out: Poly = {}
    power = ONE
    for n in range(1, CAP + 1):
        power = mul(power, a)
        out = add(out, scale(power, Q((-1) ** (n + 1), n)))
    return out


def comm(p: Poly, q: Poly) -> Poly:
    return add(mul(p, q), scale(mul(q, p), -1))


def matrix_mul(a: list[list[Q]], b: list[list[Q]]) -> list[list[Q]]:
    return [[sum((a[i][k] * b[k][j] for k in range(2)), Q(0))
             for j in range(2)] for i in range(2)]


def matrix_add(a: list[list[Q]], b: list[list[Q]], factor: Q = Q(1)) -> list[list[Q]]:
    return [[a[i][j] + factor * b[i][j] for j in range(2)] for i in range(2)]


def main() -> None:
    checks: dict[str, bool] = {}
    x, y, z = (atom(s, 3) for s in ("x", "y", "z"))
    x6, y6, z6 = (atom(s, 6) for s in ("x6", "y6", "z6"))
    X, Y, Z = add(x, x6), add(y, y6), add(z, z6)
    raw = log1(mul(mul(exp0(X), exp0(Z)), exp0(Y)))
    expected = add(X, Z, Y, scale(add(comm(x, z), comm(x, y), comm(z, y)), Q(1, 2)))
    checks["unreduced_BCH_through_six"] = raw == expected

    Zmatched = add(scale(add(x, y), -1), z6)
    reduced = log1(mul(mul(exp0(X), exp0(Zmatched)), exp0(Y)))
    expected_reduced = add(x6, z6, y6, scale(comm(x, y), Q(-1, 2)))
    checks["complete_cubic_reduction_negative_half_bracket"] = reduced == expected_reduced
    checks["dropping_cross_region_bracket_is_detected"] = reduced != add(x6, z6, y6)
    checks["unmatched_full_cubic_cannot_use_reduced_formula"] = raw != expected_reduced

    a, c = atom("a", 3), atom("c", 6)
    body_log = log1(add(ONE, a, c))
    checks["log_body_quadratic_curvature"] = body_log == add(a, c, scale(mul(a, a), Q(-1, 2)))
    checks["dropping_body_curvature_is_detected"] = body_log != add(a, c)

    T = [[Q(1), Q(1)], [Q(0), Q(1)]]
    Ti = [[Q(1), Q(-1)], [Q(0), Q(1)]]
    D = [[Q(0), Q(0)], [Q(1), Q(0)]]
    A = matrix_mul(D, Ti)
    L = [[Q(2), Q(3)], [Q(5), Q(7)]]
    LT = matrix_mul(L, T)
    projected_log = matrix_add(L, A, -LT[1][0])
    projected_endpoint = matrix_add(LT, D, -LT[1][0])
    checks["projection_transport_by_right_T"] = projected_log == matrix_mul(projected_endpoint, Ti)
    incorrectly_unchanged = matrix_add(L, D, -L[1][0])
    checks["unchanged_endpoint_projection_is_detected"] = projected_log != incorrectly_unchanged
    checks["projection_kills_normalized_body_tangent"] = matrix_add(A, A, -matrix_mul(A, T)[1][0]) == [[Q(0), Q(0)], [Q(0), Q(0)]]

    d, r, change = 7, 11, 13
    q = d * r
    checks["scalar_boundary_example_fails_strict_threshold"] = not q > r * d
    checks["reparameterization_does_not_improve_ratio"] = Q(q, r) == Q(q * change, r * change)

    payload = {
        "scope": "Exact free-algebra/rational-matrix/scalar controls; not source verification",
        "check_count": len(checks),
        "checks": checks,
        "all_passed": all(checks.values()),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "limitations": ["No G4 source solution", "No physical Hessian evaluation", "No Lean or Rust execution", "No independent review"],
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    if not payload["all_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
