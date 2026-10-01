#!/usr/bin/env python3
"""Exact finite controls for the G4 one-independent-bigon submission.

These are rational arithmetic implementation checks, not a proof of the universal
all-copy theorem. Run with Python 3.10+; only the standard library is required.
"""
from __future__ import annotations

from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from math import comb, prod
from pathlib import Path
import json
import platform


def lam(k: int) -> int:
    return k * (k - 1) // 2


@lru_cache(maxsize=None)
def p_coeff(k: int, r: int) -> tuple[tuple[int, Q], ...]:
    """Return nonzero (degree, coefficient) terms of Kingman P[k,r]."""
    if k == 0:
        return ((0, Q(1)),) if r == 0 else ()
    if not 1 <= r <= k:
        return ()
    numerator = prod(lam(j) for j in range(r + 1, k + 1))
    return tuple(
        (lam(j), Q(numerator, prod(lam(l) - lam(j)
                                 for l in range(r, k + 1) if l != j)))
        for j in range(r, k + 1)
    )


@lru_cache(maxsize=None)
def p(k: int, r: int, x: Q) -> Q:
    return sum((c * x**d for d, c in p_coeff(k, r)), Q(0))


@lru_cache(maxsize=None)
def b(k: int, r: int, x: Q, y: Q, g: Q) -> Q:
    """Count law after a bare independent bigon, starting with k roots."""
    h = 1 - g
    return sum((Q(comb(k, s)) * g**s * h**(k-s)
                * sum((p(s, a, x) * p(k-s, r-a, y)
                       for a in range(r+1)), Q(0))
                for s in range(k+1)), Q(0))


def a(k: int, x: Q, y: Q, g: Q) -> Q:
    if k < 2:
        raise ValueError("The full-merger formula is used for k >= 2.")
    return g**k * p(k, 1, x) + (1-g)**k * p(k, 1, y)


@lru_cache(maxsize=None)
def clade(k: int, u: Q) -> Q:
    return sum((p(k, r, u) * Q(2, r*(r+1))
                for r in range(1, k+1)), Q(0))


def response(k: int, z: Q, u: Q, theta: tuple[Q, Q, Q]) -> Q:
    """Legal A-clade response of E(z) * B(theta) * E(u)."""
    x, y, g = theta
    return sum((p(k, i, z) * b(i, j, x, y, g) * clade(j, u)
                for i in range(1, k+1) for j in range(1, i+1)), Q(0))


def interpolate_at_one(nodes: list[Q]) -> list[Q]:
    if len(set(nodes)) != len(nodes) or any(not 0 < z < 1 for z in nodes):
        raise ValueError("Use distinct, strictly positive finite-edge survivals.")
    return [prod(((1-y)/(x-y) for j, y in enumerate(nodes) if j != i), start=Q(1))
            for i, x in enumerate(nodes)]


def solve(matrix: list[list[Q]], rhs: list[Q]) -> list[Q]:
    """Exact Gauss-Jordan elimination; singular matrices raise an error."""
    n = len(rhs)
    if len(matrix) != n or any(len(row) != n for row in matrix):
        raise ValueError("Expected a square system.")
    aug = [list(row) + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((i for i in range(col, n) if aug[i][col] != 0), None)
        if pivot is None:
            raise ValueError("Singular observation matrix.")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        aug[col] = [v/scale for v in aug[col]]
        for i in range(n):
            if i == col:
                continue
            scale = aug[i][col]
            aug[i] = [v-scale*w for v, w in zip(aug[i], aug[col])]
    return [row[-1] for row in aug]


def run() -> dict:
    fixtures = [
        (Q(1,2), Q(3,4), Q(1,3)),
        (Q(1,2), Q(1,2), Q(1,2)),
        (Q(1,4), Q(3,4), Q(1,2)),
        (Q(1,2), Q(1,2), Q(1,3)),
        (Q(9,10), Q(1,3), Q(13,25)),
    ]
    counts = dict(positive_source_fixtures=len(fixtures), count_rows_checked=0,
                  swap_coordinates_checked=0, full_merge_coordinates_checked=0,
                  legal_observation_evaluations=0, recovered_count_rows=0,
                  recovered_count_coordinates=0, clade_leading_coefficients=0,
                  equal_weight_recoveries=0, original_id_program_coordinates=0)
    rows = []
    for theta in fixtures:
        x, y, g = theta
        assert all(0 < v < 1 for v in theta)
        for k in range(0, 9):
            values = [b(k, r, x, y, g) for r in range(k+1)]
            assert sum(values) == 1 and all(v >= 0 for v in values)
            counts['count_rows_checked'] += 1
            for r, value in enumerate(values):
                assert value == b(k, r, y, x, 1-g)
                counts['swap_coordinates_checked'] += 1
            if k >= 2:
                assert b(k, 1, x, y, g) == a(k, x, y, g)
                counts['full_merge_coordinates_checked'] += 1
        for k in range(2, 7):
            z_nodes = [Q(i, lam(k)+2) for i in range(1, lam(k)+2)]
            weights = interpolate_at_one(z_nodes)
            assert sum(weights) == 1
            u_nodes = [Q(1,2)**i for i in range(1, k+1)]
            readings = []
            for u in u_nodes:
                physical = [response(k, z, u, theta) for z in z_nodes]
                assert all(0 <= v <= 1 for v in physical)
                counts['legal_observation_evaluations'] += len(physical)
                readings.append(sum((w*v for w, v in zip(weights, physical)), Q(0)))
            matrix = [[clade(j, u) for j in range(1, k+1)] for u in u_nodes]
            recovered = solve(matrix, readings)
            direct = [b(k, j, x, y, g) for j in range(1, k+1)]
            assert recovered == direct
            assert recovered[0] == a(k, x, y, g)
            counts['recovered_count_rows'] += 1
            counts['recovered_count_coordinates'] += len(recovered)
            rows.append(dict(theta=[str(v) for v in theta], entering_copies=k,
                             total_four_taxon_copies=k+3,
                             positive_tests=len(z_nodes)*len(u_nodes),
                             full_merge=str(recovered[0])))
        # One shared locus-wide program draw; never resample it by lineage.
        programs = [(Q(1),Q(0),Q(0)), (Q(1,3),Q(1,3),Q(1,3)),
                    (Q(1,2),Q(1,3),Q(1,6)), (Q(0),Q(1),Q(0))]
        for alpha, beta, gamma in programs:
            assert alpha+beta+gamma == 1
            for k in range(2,6):
                for r in range(1,k+1):
                    left = alpha*b(k,r,x,y,g)+beta*p(k,r,x)+gamma*p(k,r,y)
                    right = alpha*b(k,r,y,x,1-g)+beta*p(k,r,y)+gamma*p(k,r,x)
                    assert left-right == (beta-gamma)*(p(k,r,x)-p(k,r,y))
                    counts['original_id_program_coordinates'] += 1
        if g == Q(1,2):
            s = 2-4*a(2,x,y,g)
            t = 16*a(3,x,y,g)-4+3*s
            xy = (s**3-t)/(3*s)
            assert s == x+y and xy == x*y
            counts['equal_weight_recoveries'] += 1
    for k in range(1, 17):
        leading = sum((next((c for d,c in p_coeff(k,r) if d == lam(k)), Q(0))
                       * Q(2,r*(r+1)) for r in range(1,k+1)), Q(0))
        expected = Q(1) if k == 1 else (Q(-2,3) if k == 2 else
                    Q((-1)**(k-1)*2, (k-1)*comb(2*k-2,k-1)))
        assert leading == expected and leading != 0
        counts['clade_leading_coefficients'] += 1
    theta = (Q(1,4),Q(3,4),Q(1,2))
    eta = (Q(1,2),Q(1,2),Q(1,2))
    assert a(2,*theta) == a(2,*eta) == Q(1,4)
    delta = a(3,*theta)-a(3,*eta)
    assert delta == Q(3,256)
    return {
        'status':'PASS', 'arithmetic':'fractions.Fraction; exact rational arithmetic',
        'python':platform.python_version(),
        'verify_py_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'counts':counts,
        'negative_control':{'same_a2':'1/4','a3_difference':str(delta),
                            'scope':'merger summaries only'},
        'rows':rows,
        'limits':[
            'Finite controls are not an all-copy proof or independent review.',
            'Count kernels, not a complete labelled-forest implementation, are checked.',
            'No uniform one-bigon cutoff was computed by this Python script.',
            'Arbitrary independent serial-chain equivalence is not implemented.',
            'The Wolfram exact CAD checks are reported separately.'
        ]
    }


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
