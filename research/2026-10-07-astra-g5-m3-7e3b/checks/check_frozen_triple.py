#!/usr/bin/env python3
"""Exact symbolic frozen-triple check, NOT a Lean or whole-source certificate.

Generates current-ancestor merger transitions from set partitions rather than
transcribing the candidate ODE. Invalid hidden-state combinations are unused
absorbing rows. All five candidate probabilities are checked against the
resulting finite generator, at zero, at infinity, and for normalization.
"""
from __future__ import annotations
import hashlib
import json
import platform
import sys
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path
import sympy as sp

PARTITIONS = (
    ((0,), (1,), (2,)), ((0, 1), (2,)), ((0, 2), (1,)),
    ((0,), (1, 2)), ((0, 1, 2),),
)
RATE, AGE = sp.symbols('rate age', positive=True)
Q = sp.exp(-RATE * AGE)


def canonical(blocks):
    return tuple(sorted(tuple(sorted(block)) for block in blocks))


def generator(occupancy: int, *, erroneous_copy_rates: bool = False):
    """Per-current-ancestor-pair rate, with hidden populations fixed."""
    positions = {tip: p for p, block in enumerate(PARTITIONS[occupancy]) for tip in block}
    g = sp.zeros(5, 5)
    for state_index, state in enumerate(PARTITIONS):
        assigned = []
        for block in state:
            population_set = {positions[x] for x in block}
            if len(population_set) != 1:
                break
            assigned.append(next(iter(population_set)))
        else:
            for a in range(len(state)):
                for b in range(a + 1, len(state)):
                    if assigned[a] != assigned[b]:
                        continue
                    merged = [block for i, block in enumerate(state) if i not in (a, b)]
                    merged.append(state[a] + state[b])
                    target = PARTITIONS.index(canonical(merged))
                    multiplicity = len(state[a]) * len(state[b]) if erroneous_copy_rates else 1
                    g[state_index, target] += RATE * multiplicity
            g[state_index, state_index] = -sum(g[state_index, j] for j in range(5) if j != state_index)
    return g


def candidate(occupancy: int):
    if occupancy == 0:
        return sp.Matrix([[1, 0, 0, 0, 0]])
    if occupancy == 4:
        pair = (Q - Q**3) / 2
        return sp.Matrix([[Q**3, pair, pair, pair, 1 - 3*pair - Q**3]])
    out = [sp.Integer(0)] * 5
    out[0], out[occupancy] = Q, 1-Q
    return sp.Matrix([out])


def ensure_zero(expr, label: str):
    residual = sp.simplify(sp.expand(expr))
    if residual != 0:
        raise AssertionError(f'{label}: nonzero residual {residual}')


def main() -> int:
    counts = {'generator_row_sum': 0, 'forward_ode_coordinates': 0,
              'initial_coordinates': 0, 'infinite_time_coordinates': 0,
              'probability_row_normalizations': 0, 'polynomial_factors': 0,
              'rational_posterior_families': 0, 'rational_endpoint_support_tests': 0}
    for hidden in range(5):
        g, p = generator(hidden), candidate(hidden)
        for i in range(5):
            ensure_zero(sum(g[i, j] for j in range(5)), f'generator row {hidden}/{i}')
            counts['generator_row_sum'] += 1
        residual = sp.diff(p, AGE) - p*g
        for j in range(5):
            ensure_zero(residual[j], f'ODE {hidden}/{j}')
            counts['forward_ode_coordinates'] += 1
            ensure_zero(p[j].subs(AGE, 0) - int(j == 0), f'initial {hidden}/{j}')
            counts['initial_coordinates'] += 1
            ensure_zero(sp.limit(p[j], AGE, sp.oo) - int(j == hidden), f'limit {hidden}/{j}')
            counts['infinite_time_coordinates'] += 1
        ensure_zero(sum(p) - 1, f'normalization {hidden}')
        counts['probability_row_normalizations'] += 1
    q = sp.symbols('q', real=True)
    pair, full = (q-q**3)/2, 1-sp.Rational(3, 2)*q+sp.Rational(1, 2)*q**3
    ensure_zero(pair - q*(1-q)*(1+q)/2, 'pair nonnegative factor')
    ensure_zero(full - (1-q)**2*(q+2)/2, 'full nonnegative factor')
    counts['polynomial_factors'] = 2

    # Posterior weights need not factor. Every positive numerator remains
    # positive after normalization. All arithmetic here is exact rational.
    for a in (Fraction(1, 17), Fraction(2, 5), Fraction(9, 10)):
        for b in (Fraction(1, 11), Fraction(3, 7), Fraction(7, 8)):
            prior = [a*b, a*(1-b), (1-a)*b, (1-a)*(1-b)]
            for shift in range(5):
                occupancy = [(i+shift) % 5 for i in range(4)]
                survival = [Fraction(1, 2+i+shift) for i in range(4)]
                numerator = [prior[i]*survival[i] for i in range(4)]
                posterior = [x/sum(numerator) for x in numerator]
                if not all(x > 0 for x in posterior) or sum(posterior) != 1:
                    raise AssertionError('positive normalization failed')
                counts['rational_posterior_families'] += 1
                for j in range(5):
                    mass = sum((posterior[i] for i in range(4) if occupancy[i] == j), Fraction(0))
                    if (mass > 0) != (j in occupancy):
                        raise AssertionError('endpoint support mismatch')
                    counts['rational_endpoint_support_tests'] += 1

    # Negative controls: a wrong live-ancestor semantics must not pass, and
    # dropped positivity assumptions must break the endpoint/support step.
    wrong_residual = sp.diff(candidate(4), AGE) - candidate(4)*generator(4, erroneous_copy_rates=True)
    wrong_nonzero = [str(sp.simplify(x)) for x in wrong_residual if sp.simplify(x) != 0]
    if not wrong_nonzero:
        raise AssertionError('erroneous original-copy pair rates escaped detection')
    zero_rate_limit = [int(x.subs(RATE, 0)) for x in candidate(4)]
    if zero_rate_limit == [0, 0, 0, 0, 1]:
        raise AssertionError('zero-rate negative control failed')
    zero_weight_support = [j for j in range(5) if sum(w for h, w in zip((0, 4), (1, 0)) if h == j) > 0]
    if zero_weight_support != [0]:
        raise AssertionError('zero-weight negative control failed')
    source = Path(__file__)
    report = {
        'status': 'PASS', 'utc': datetime.now(timezone.utc).isoformat(),
        'claim_category': 'exact symbolic finite frozen-three-label kernel and rational controls only',
        'python': platform.python_version(), 'sympy': sp.__version__,
        'checker_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'counts': counts,
        'negative_controls': {
            'wrong_original_copy_rate_rejected': True,
            'nonzero_ode_residuals': wrong_nonzero,
            'zero_rate_absorption_rejected': True,
            'zero_rate_endpoint': zero_rate_limit,
            'zero_weight_occupancy_loss': {'hidden_occupancies': [0, 4], 'weights': [1, 0],
                                         'limiting_support': zero_weight_support},
        },
        'not_proved': ['Lean elaboration or kernel acceptance',
            'actual original-network conditional event-free source/kernel identity',
            'observable germ analytic continuation in Lean',
            'complete M3 full-cluster/split endpoint', 'any minimum M3 threshold'],
    }
    print(json.dumps(report, indent=2))
    return 0

if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        raise
