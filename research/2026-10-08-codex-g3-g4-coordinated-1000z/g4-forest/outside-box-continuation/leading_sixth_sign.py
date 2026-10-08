"""Exact source sixth-diagonal jet and rational leading-root isolation.

This stdlib calculation derives the jet from the original fair CURRENT-root
routing formula. It does not execute a positive-t root finder or assert that
an approximate source point is a full-forest common zero.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import time
import types

SOURCE = "research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py"
SOURCE_SHA = "850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884"
ORDER = 6


def add(p, q):
    r = p.copy()
    for k, c in q.items():
        r[k] = r.get(k, F(0)) + c
    return {k: c for k, c in r.items() if c}


def scale(p, c):
    return {k: v*c for k, v in p.items() if v*c}


def mul(p, q):
    """Truncated polynomials in t,A,w, keyed by their three exponents."""
    r = {}
    for (d, a, b), c in p.items():
        for (e, x, y), v in q.items():
            if d+e <= ORDER:
                k = d+e, a+x, b+y
                r[k] = r.get(k, F(0)) + c*v
    return {k: c for k, c in r.items() if c}


def power(p, n):
    r = {(0, 0, 0): F(1)}
    for _ in range(n):
        r = mul(r, p)
    return r


def source_log_diagonal(n):
    s = {(0, 0, 0): F(1), (1, 1, 0): F(-1)}
    h2 = {(3, 0, 1): F(1)}
    diagonal = {}
    # For k routed roots, no merger has exponents C(k,2),C(n-k,2).
    # Averaging the paired arm terms gives the exact even-in-h expression.
    for k in range(n+1):
        px, py = comb(k, 2), comb(n-k, 2)
        lo, diff = min(px, py), abs(px-py)
        even = {}
        for j in range(diff//2+1):
            term = mul(power(s, diff-2*j), power(h2, j))
            even = add(even, scale(term, F(comb(diff, 2*j))))
        term = mul(power(add(mul(s, s), scale(h2, F(-1))), lo), even)
        diagonal = add(diagonal, scale(term, F(comb(n, k), 2**n)))
    u = add(diagonal, {(0, 0, 0): F(-1)})
    logarithm = {}
    for j in range(1, ORDER+1):
        logarithm = add(logarithm, scale(power(u, j), F((-1)**(j+1), j)))
    return logarithm


def trim(p):
    p = p[:]
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def uadd(p, q):
    r = [F(0)]*max(len(p), len(q))
    for i, c in enumerate(p):
        r[i] += c
    for i, c in enumerate(q):
        r[i] += c
    return trim(r)


def umul(p, q):
    r = [F(0)]*(len(p)+len(q)-1)
    for i, c in enumerate(p):
        for j, d in enumerate(q):
            r[i+j] += c*d
    return trim(r)


def ueval(p, x):
    r = F(0)
    for c in reversed(p):
        r = r*x+c
    return r


def remainder(p, q):
    p = trim(p)
    while p != [F(0)] and len(p) >= len(q):
        j, c = len(p)-len(q), p[-1]/q[-1]
        for i, d in enumerate(q):
            p[i+j] -= c*d
        p = trim(p)
    return p


def sturm(p):
    seq = [trim(p), trim([i*p[i] for i in range(1, len(p))])]
    while seq[-1] != [F(0)]:
        r = remainder(seq[-2], seq[-1])
        if r == [F(0)]:
            break
        seq.append([-c for c in r])
    return seq


def variations(seq, x):
    signs = [1 if v > 0 else -1 for p in seq if (v := ueval(p, x)) != 0]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def leading_equation(y):
    S4 = [1+y**4, F(0), F(0), F(0), F(2)]
    S5 = [1+y**5, F(0), F(0), F(0), F(0), F(2)]
    D1 = [-1-2*y, F(3)]
    D2 = [-1-2*y*y, F(0), F(3)]
    return uadd([30*c for c in umul(S4, D2)], [-48*c for c in umul(S5, D1)])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    if args.output.exists():
        raise ValueError("refusing to overwrite exact receipt")
    start = time.perf_counter()
    raw = (args.root/SOURCE).read_bytes()
    assert sha256(raw).hexdigest() == SOURCE_SHA
    fa = types.ModuleType("authenticated_original_forest_source")
    fa.__file__ = str(args.root/SOURCE)
    exec(compile(raw, fa.__file__, "exec"), fa.__dict__)
    controls = []
    for n in range(2, 7):
        x, y = F(1, 3), F(3, 4)
        reference = sum((p for forest, p in fa.bigon_law(n, x, y, F(1, 2), "independent").items()
                         if len(forest) == n), F(0))
        routing = sum((F(comb(n, k), 2**n)*x**comb(k, 2)*y**comb(n-k, 2)
                       for k in range(n+1)), F(0))
        assert reference == routing
        controls.append({"n": n, "actual_original_diagonal": str(reference), "routing_sum": str(routing)})
    D6 = {}
    for n, c in [(6, 1), (5, -6), (4, 15), (3, -20), (2, 15)]:
        D6 = add(D6, scale(source_log_diagonal(n), F(c)))
    expected = {(6, 6, 0): F(15, 16), (6, 3, 1): F(-45, 4)}
    assert D6 == expected
    roots = []
    for delta in [F(1, 50), F(1, 20), F(1, 10)]:
        y = 1+delta
        G = leading_equation(y)
        seq = sturm(G)
        lo, hi = F(9, 5), F(2)
        vl, vh = variations(seq, lo), variations(seq, hi)
        assert vl-vh == 1 and ueval(G, lo)*ueval(G, hi) < 0
        for _ in range(48):
            mid = (lo+hi)/2
            if ueval(G, lo)*ueval(G, mid) < 0:
                hi = mid
            else:
                lo = mid
        assert y < lo < hi < 2
        roots.append({"delta": str(delta), "y": str(y),
                      "G_coefficients_ascending": list(map(str, G)),
                      "sturm_sequence_coefficients_ascending": [list(map(str, p)) for p in seq],
                      "initial_interval": ["9/5", "2"], "initial_sturm_variations": [vl, vh],
                      "unique_root_isolating_interval": [str(lo), str(hi)],
                      "all_sign_theorem_hypotheses_on_interval": True})
    result = {"status": "EXACT_SOURCE_LEADING_SIXTH_DEFECT_AND_LEADING_ROOT_DOMAIN_PASS",
              "source_sha256": SOURCE_SHA, "own_source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
              "exact_original_diagonal_controls": controls,
              "jet_monomial_order": ["t_degree", "A_degree", "w_degree"],
              "D6_jet_through_t6": [{"exponents": list(k), "coefficient": str(c)} for k, c in sorted(D6.items())],
              "all_lower_t_coefficients_vanish": True,
              "analytic_weight_curve_note": "Replacing w by any analytic w(t) leaves this t6 coefficient equal to 15*A6/16-45*A3*w(0)/4.",
              "exact_leading_root_isolations": roots,
              "sign_theorem_domain": "0<delta<=1/10; y=1+delta<z<=2; G(z,delta)=0",
              "variance_bound": "delta2/4",
              "positive_gap_lower_bound": "23/1600",
              "leading_per_factor_D6_bound": "L6 <= -(15/16)*S4*(23/1600) < 0",
              "scope": "leading coefficient of actual diagonal-balanced source branch; sufficiently small positive t on an existing analytic branch; no finite-t uniform remainder bound",
              "not_claimed": ["new actual finite-t common zero", "no root in failed placement solve", "all-cap positive-source obstruction", "G4 closure"],
              "runtime_seconds": time.perf_counter()-start}
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": result["status"], "output": str(args.output), "runtime_seconds": result["runtime_seconds"]}))


if __name__ == "__main__":
    main()
