"""Attributed outside-box derivative of role6's authenticated cap5 extractor.

The accepted eight-cell source family's implicit equations are evaluated in
the complete ten-shape current-root forest algebra. All physical parameters
are shared over arities. An approximate common zero is never labelled exact.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import time
import types

import mpmath as mp

HELPER = "research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-forest/exact_forest_layer.py"
HELPER_SHA = "e0ced6748fd6fbe27f8165446a1c63a09bdb598fd1bdcd89115d4ae4853193b8"
RETURN = "research/2026-10-08-cloud-g4-eight-cell-0704z/ACTUAL-EIGHT-CELL-FULL-FIVE-RETURN.md"
RETURN_SHA = "20e6b92a6039db24faee986f354428d8936fb3b992d2eaec24192d538f50ae81"


def load_helper(root):
    p = root / HELPER
    raw = p.read_bytes()
    if sha256(raw).hexdigest() != HELPER_SHA:
        raise ValueError("authenticated helper identity mismatch")
    if sha256((root / RETURN).read_bytes()).hexdigest() != RETURN_SHA:
        raise ValueError("accepted return source identity mismatch")
    h = types.ModuleType("read_only_authenticated_forest_helper")
    h.__file__ = str(p)
    exec(compile(raw, str(p), "exec"), h.__dict__)
    return h


def real(q):
    q = Fraction(q)
    return mp.mpf(q.numerator) / q.denominator


class Source:
    def __init__(self, h, fa):
        self.h = h
        self.states = [h.representative(s, fa) for s in h.SHAPES5]
        index = {s: i for i, s in enumerate(h.SHAPES5)}
        self.E = h.ordinary_polynomials(self.states, index, fa)
        self.B = h.bigon_polynomials(self.states, index, fa)
        self.ec = [[[(k, real(v)) for k, v in p.items()] for p in row] for row in self.E]
        self.bc = [[[(p, q, real(c)) for (p, q), c in poly.items() if p >= q]
                    for poly in row] for row in self.B]
        self.delete = [[real(q) for q in row] for row in (
            [1, Fraction(2, 5), 0, 0, 0, 0, 0, 0, 0, 0],
            [0, Fraction(3, 5), Fraction(4, 5), Fraction(3, 5), 0, 0, 0, 0, 0, 0],
            [0, 0, 0, Fraction(2, 5), Fraction(2, 5), Fraction(4, 5), Fraction(4, 5), 0, 0, 0],
            [0, 0, Fraction(1, 5), 0, Fraction(3, 5), 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, Fraction(1, 5), 0, Fraction(1, 5), 0, Fraction(3, 5)],
            [0, 0, 0, 0, 0, 0, Fraction(1, 5), Fraction(4, 5), 1, Fraction(2, 5)],
        )]

    def ordinary(self, z):
        return [[mp.fsum(c * z**e for e, c in p) for p in row] for row in self.ec]

    def branch(self, A, w, t):
        s = 1 - A*t
        h2 = w*t**3
        values = {}
        for row in self.bc:
            for poly in row:
                for p, q, _ in poly:
                    if (p, q) in values:
                        continue
                    d = p-q
                    v = (s*s-h2)**q
                    if d:
                        v *= 2*mp.fsum(comb(d, 2*j)*s**(d-2*j)*h2**j
                                       for j in range(d//2+1))
                    values[p, q] = v
        return [[mp.fsum(c*values[p, q] for p, q, c in poly)
                 for poly in row] for row in self.bc]

    def vm(self, row, matrix):
        return [mp.fsum(row[k]*matrix[k][j] for k in range(10)) for j in range(10)]

    def residual_coordinates(self, row):
        q4 = [mp.fsum(c*p for c, p in zip(r, row)) for r in self.delete]
        C = q4[3] - (q4[2]+q4[3])/3
        H = q4[4] - (q4[4]+q4[5])/3
        return [C, C+H, row[7], row[8], row[9]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[4])
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--precision", type=int, default=100)
    ap.add_argument("--t", default="1/10000")
    ap.add_argument("--delta",required=True)
    args = ap.parse_args()
    if args.output.exists():
        raise ValueError("refusing to overwrite saved result")
    mp.mp.dps = args.precision
    started = time.perf_counter()
    h = load_helper(args.root)
    fa, original_sha = h.load_source(args.root)
    src = Source(h, fa)
    t = real(args.t)
    delta, rho, d, a, b = real(args.delta), real("3/2"), real("1/4"), real("1/2"), real("1/2")
    y = 1+delta
    def G(z):
        S4, S5 = 1+y**4+2*z**4, 1+y**5+2*z**5
        return 30*S4*(3*z*z-1-2*y*y)-48*S5*(3*z-1-2*y)
    z = mp.findroot(G, (mp.mpf("1.8"), mp.mpf("1.9")))
    p = (1+y**4+2*z**4)/(48*(3*z-1-2*y))
    A = [mp.mpf(1), y, z, z]
    w0 = [mp.mpf(1)/6+2*p, y**3/6+4*p, z**3/6-2*p, z**3/6-4*p]
    powers = [5, 6, 7, 9, 10]
    def moments(*c):
        return [1-2*c[0]**k+2*c[1]**k-2*c[2]**k+2*c[3]**k-2*c[4]**k+rho**k for k in powers]
    guesses = [1+(rho-1)*(1-mp.cos(mp.pi*(j+1)/6))/2 for j in range(5)]
    roots = list(mp.findroot(moments, guesses, tol=mp.mpf(10)**(-args.precision+20)))
    if not (1 < roots[0] < roots[1] < roots[2] < roots[3] < roots[4] < rho):
        raise ValueError("leading moment roots lack strict order")
    scale = (1/b)/roots[2]
    L, C1, C2, _, C4, C5, U = [v*scale for v in [1, *roots, rho]]
    initial_theta = [L, C1, C2, C4, C5]
    q = [1-aa*t/2 for aa in A]
    def diagonal_equations(*w3):
        w = [*w3, w0[3]]
        logs = []
        for n in range(2, 6):
            totals = []
            for aa, ww in zip(A, w):
                s, h2 = 1-aa*t, ww*t**3
                # symmetric original routing polynomial, exactly even in h.
                v = mp.mpf(0)
                for k in range(n+1):
                    px, py = comb(k, 2), comb(n-k, 2)
                    lo, diff = min(px, py), abs(px-py)
                    sym = (s*s-h2)**lo * mp.fsum(comb(diff, 2*j)*s**(diff-2*j)*h2**j for j in range(diff//2+1))
                    # paired k and n-k have equal coefficients; each single
                    # term gets the half symmetric sum, valid also px=py.
                    v += comb(n, k)*sym/(2**n)
                totals.append(mp.log(v))
            logs.append(mp.fsum(totals))
        ell2, ell3, ell4, ell5 = logs
        return [(ell3-3*ell2)/t**3,
                (ell4-4*ell3+6*ell2)/t**4,
                (ell5-5*ell4+10*ell3-10*ell2)/t**5]
    w3 = list(mp.findroot(diagonal_equations, w0[:3], tol=mp.mpf(10)**(-args.precision+25),maxsteps=50))
    w = [*w3, w0[3]]
    branches = [src.branch(aa, ww, t) for aa, ww in zip(A, w)]
    seam = mp.exp(-t)
    def source_factors(theta):
        X1, X2, X3, X6, X7 = theta
        X4, X5 = q[0]*seam/b, 1/(b*seam)
        # P (target a), then R (target b), oldest to youngest.
        edgesP = [a*b*U/q[2], X7/(q[1]*U), X6/(q[3]*X7), X5/(q[0]*X6), seam]
        edgesR = [seam, X3/(q[3]*X4), X2/(q[1]*X3), X1/(q[2]*X2), 1/X1]
        factors = []
        for labels, edges in [([2, 1, 3, 0], edgesP), ([0, 3, 1, 2], edgesR)]:
            factors.append(src.ordinary(edges[0]))
            for j, label in enumerate(labels):
                factors.extend([branches[label], src.ordinary(edges[j+1])])
        return factors, edgesP+edgesR
    def law(theta, normalized):
        row = src.ordinary(1/d)[0] if normalized else [mp.mpf(1)]+[mp.mpf(0)]*9
        for factor in source_factors(theta)[0]:
            row = src.vm(row, factor)
        return row
    def placement_equations(*theta):
        return [v/t**3 for v in src.residual_coordinates(law(theta, True))]
    theta = list(mp.findroot(placement_equations, initial_theta, tol=mp.mpf(10)**(-args.precision+20), maxsteps=60))
    K, N = law(theta, False), law(theta, True)
    ordinary = src.ordinary(d)[0]
    edges = source_factors(theta)[1]
    arms = [(1-aa*t-mp.sqrt(ww)*t**mp.mpf("1.5"), 1-aa*t+mp.sqrt(ww)*t**mp.mpf("1.5")) for aa, ww in zip(A,w)]
    cell_b6=[]
    for aa,ww in zip(A,w):
        s,h2=1-aa*t,ww*t**3
        v=mp.mpf(0)
        for k in range(7):
            px,py=comb(k,2),comb(6-k,2)
            lo,diff=min(px,py),abs(px-py)
            sym=(s*s-h2)**lo*mp.fsum(comb(diff,2*j)*s**(diff-2*j)*h2**j for j in range(diff//2+1))
            v+=mp.mpf(comb(6,k))/64*sym
        cell_b6.append(v)
    Delta6=2*mp.fsum(mp.log(bb)-15*mp.log(qq) for bb,qq in zip(cell_b6,q))
    leading_D6=-mp.mpf(15)/16*mp.fsum(aa**6 for aa in A)+mp.mpf(45)/2*p*(3*z**3-1-2*y**3)
    physical_values = [*edges, *(v for pair in arms for v in pair)]
    if min(w) <= 0 or not all(0 < v < 1 for v in physical_values):
        raise ValueError("numerical candidate fails strict physical margins")
    # This derivative is an observed high-precision Jacobian, not an enclosure.
    J = mp.matrix(mp.diff(lambda *u: placement_equations(*u), tuple(theta))) if False else mp.matrix(5, 5)
    for j in range(5):
        for i in range(5):
            def one(v):
                u = theta.copy(); u[j] = v
                return placement_equations(*u)[i]
            J[i, j] = mp.diff(one, theta[j])
    def fmt(v):
        return mp.nstr(v, args.precision)
    result = {
        "status": "AUTHENTICATED_SOURCE_HIGH_PRECISION_APPROXIMATE_COMMON_ZERO_ONLY",
        "original_source_sha256": original_sha, "helper_sha256": HELPER_SHA,
        "accepted_return_sha256": RETURN_SHA, "own_source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "mpmath_version": mp.__version__, "precision_decimal_digits": args.precision,
        "fixed_inputs": {"d": "1/4", "a": "1/2", "b": "1/2", "delta": args.delta, "rho": "3/2", "t": args.t},
        "inherited_extractor_sha256":"d4ec5d39d21ffcf500c660eaf453f770b827cebc2d34f4c01dfe99f4ba342113",
        "means": list(map(fmt,A)), "z_equation_residual": fmt(G(z)), "p": fmt(p),
        "leading_weights": list(map(fmt,w0)), "weights": list(map(fmt,w)),
        "leading_unscaled_switch_roots": list(map(fmt,roots)), "leading_moment_residual": list(map(fmt,moments(*roots))),
        "leading_theta": list(map(fmt,initial_theta)), "fixed_U": fmt(U), "theta": list(map(fmt,theta)),
        "cells_chronological_labels_one_based": [3,2,4,1,1,4,2,3],
        "arms_by_label": [[fmt(x),fmt(y)] for x,y in arms],
        "ordinary_edges_P_then_R": list(map(fmt,edges)),
        "minimum_physical_survival_margin": fmt(min(min(v,1-v) for v in physical_values)),
        "all_numerical_source_parameters_strict": True,
        "scaled_diagonal_equations": list(map(fmt,diagonal_equations(*w3))),
        "scaled_placement_equations": list(map(fmt,placement_equations(*theta))),
        "complete_fresh_cap5_orbit_row": list(map(fmt,K)), "ordinary_target_row": list(map(fmt,ordinary)),
        "full_ten_orbit_absolute_difference": list(map(fmt,[x-y for x,y in zip(K,ordinary)])),
        "max_full_orbit_difference": fmt(max(abs(x-y) for x,y in zip(K,ordinary))),
        "normalized_row": list(map(fmt,N)),
        "observed_scaled_placement_jacobian": [[fmt(J[i,j]) for j in range(5)] for i in range(5)],
        "observed_scaled_placement_jacobian_determinant": fmt(mp.det(J)),
        "cell_b6_no_merger_probabilities":list(map(fmt,cell_b6)),
        "source_Delta6_log_b6_minus_15log_pair":fmt(Delta6),
        "b6_source_minus_ordinary_target":fmt(d**15*mp.expm1(Delta6)),
        "leading_per_factor_D6_coefficient":fmt(leading_D6),
        "Delta6_divided_by_2t6":fmt(Delta6/(2*t**6)),
        "no_interval_commonzero_validation":True,
        "runtime_seconds": time.perf_counter()-started,
        "not_claimed": ["exact positive-t common zero", "interval-enclosed source centre", "certified inverse/Hessian/domain radius", "cap-six equality", "all-cap library", "controlled signed factorization", "G4 closure"]
    }
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"status":result["status"],"maximum_orbit_error":result["max_full_orbit_difference"],"minimum_margin":result["minimum_physical_survival_margin"],"runtime_seconds":result["runtime_seconds"]}))


if __name__ == "__main__":
    main()
