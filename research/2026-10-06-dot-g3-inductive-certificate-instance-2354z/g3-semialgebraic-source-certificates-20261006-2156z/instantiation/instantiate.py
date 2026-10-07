"""New exact instantiation; inherited analytic bounds are not re-executed."""
import hashlib
import json
import math
import platform
import time
from fractions import Fraction as Q
from pathlib import Path
import sympy as S

started = time.perf_counter()
here = Path(__file__).parent
providers = here.parent / 'providers'
expected = {
    'paired-normal-certificate.json': '2a9a8ab705c7fb689b0cbbf3d15e6972ecd71fe837c8926344bb950aa4c5a118',
    'paired-normal-algebra.json': '6f47205ebfe446ab08e7a63996b59f41c3be152498a8a7d25a35bc8d17bb5317',
}
for name, digest in expected.items():
    assert hashlib.sha256((providers / name).read_bytes()).hexdigest() == digest
old = json.loads((providers / 'paired-normal-certificate.json').read_text())
algebra = json.loads((providers / 'paired-normal-algebra.json').read_text())
assert old['input_normal_sha256'] == expected['paired-normal-algebra.json']
ls = [1, 3, 6, 10, 15, 21]
r = Q(1, 2)
R = {n: sum((r**j for j in range(n)), Q(0)) for n in ls}
rows = {}
scales = {}
for key in ['F0', 'F1']:
    data = old['normal_records'][key]
    assert data['exponents'] == algebra[key]['exponents']
    coeff = [Q(x) for x in data['c']]
    assert coeff == [Q(x) for x in algebra[key]['c']]
    full = [dict(zip(data['exponents'], coeff)).get(n, Q(0)) for n in ls]
    scale = math.lcm(*(c.denominator for c in full))
    ints = [int(scale*c) for c in full]
    assert all(Q(i) == scale*c for i, c in zip(ints, full))
    assert sum(ints) == scale > 0
    assert sum(c*n for c, n in zip(ints, ls)) == 0
    assert sum(c*R[n] for c, n in zip(ints, ls)) == 0
    nodes = [Q(1), r] + ([r*r] if key == 'F1' else [])
    for t in nodes:
        assert sum(c*(1-t**n) for c, n in zip(ints, ls)) == 0
        assert sum(c*n*t**(n-1) for c, n in zip(ints, ls)) == 0
    assert Q(data['coefficient_L1']) == sum(abs(c) for c in full)
    rows[key] = ints
    scales[key] = scale

c = {key: Q(value) for key, value in old['constants'].items()}
eta = c['root_interval_half_width']
width = c['near_one_width']
U = [r-eta, r+eta]
V = [r*r-eta, r*r+eta]
alpha, beta = 1-U[1], 1-V[1]
assert 0 < eta <= Q(1, 32)
assert 0 < V[0] < V[1] < U[0] < U[1] < c['Q'] < 1
assert width == 1-c['Q']
B0 = scales['F0']*c['B0']
delta = scales['F0']*c['delta']
B1 = scales['F1']*c['B1']
gamma = scales['F1']*c['gamma']
assert min(B0, delta, B1, gamma, alpha, beta, c['p0'], width) > 0
epsilon_candidates = {
    'pair_to_small_p': c['p0']*width/2,
    'first_denominator': alpha/(4*B0),
    'second_denominator': beta/(4*B1),
    'cauchy_absorption': gamma*alpha*delta**2/(16*B1*B0**2),
    'unit_cap': Q(1, 4),
}
eps = min(epsilon_candidates.values())
b = 1/(1+eps)
assert 0 < eps < c['p0']*width
assert B0*eps/alpha < Q(1, 2)
assert B1*eps/beta < Q(1, 2)
assert 8*B1*B0**2*eps/(alpha*delta**2) < gamma
assert 0 < b < 1

# These exact identities justify the universal state update margins.
B, d, P, Qv, T, V1, V2, p, b0, b1, de, ga = S.symbols('B d P Q T V1 V2 p b0 b1 delta gamma')
identities = {
    'pair_budget': ((1+B)-(1-d)*(1+B+d), d*(B+d)),
    'first_U': ((1-b0*Qv)*(1-b0*p**2)-(1-b0*(Qv+p**2)), b0**2*Qv*p**2),
    'first_V': ((1+de*V1)*(1+de*p)-(1+de*(V1+p)), de**2*V1*p),
    'second_U': ((1+ga*T)*(1+ga*p**3)-(1+ga*(T+p**3)), ga**2*T*p**3),
    'second_V': ((1-b1*V2)*(1-b1*p**2)-(1-b1*(V2+p**2)), b1**2*V2*p**2),
    'cauchy_squares': ((P*p**2+T)**2-4*Qv**2*p**2, (P*p**2-T)**2+4*p**2*(P*T-Qv**2)),
    'cauchy_update': ((P+p)*(T+p**3)-(Qv+p**2)**2, P*T-Qv**2+p*(P*p**2+T-2*Qv*p)),
    'V_square': ((V1+p)**2-(V2+p**2), V1**2-V2+2*V1*p),
}
for left, right in identities.values():
    assert S.expand(left-right) == 0

# Exact compact algebraic input, without expanding high-degree polynomials.
N = 2
while (1-Q(1, 2**N))**2 < b:
    N += 1
    assert N < 100000
t = 1-Q(1, 2**N)
exponents = [Q(n)+R[n] for n in ls]
assert t*t >= b
for row in rows.values():
    assert sum(Q(v)*e for v, e in zip(row, exponents)) == 0
assert exponents[1] != 3*exponents[0]

out = {
    'status': 'PASS exact coefficient instantiation and polynomial identities',
    'new_execution': True,
    'python': platform.python_version(),
    'sympy': S.__version__,
    'elapsed_seconds': time.perf_counter()-started,
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'source_sha256': expected,
    'exponents': ls,
    'residue': str(r),
    'integer_normal_rows': rows,
    'positive_normal_scales': scales,
    'root_intervals': {'U': list(map(str, U)), 'V': list(map(str, V))},
    'constants': {key: str(value) for key, value in {
        'alpha': alpha, 'beta': beta, 'B0': B0, 'B1': B1,
        'delta': delta, 'gamma': gamma, 'epsilon': eps, 'pair_floor_b': b,
    }.items()},
    'epsilon_candidates': {key: str(value) for key, value in epsilon_candidates.items()},
    'verified_strict_ratios': {
        'B0_epsilon_over_alpha': str(B0*eps/alpha),
        'B1_epsilon_over_beta': str(B1*eps/beta),
        'absorption_over_gamma': str(8*B1*B0**2*eps/(alpha*delta**2*gamma)),
    },
    'symbolic_margin_identities': {key: {'left': str(left), 'right': str(right)} for key, (left, right) in identities.items()},
    'target': {
        'base': str(t), 'base_formula': f'1-2^(-{N})', 'N': N,
        'coordinate_encoding': ['base^('+str(e)+')' for e in exponents],
        'first_coordinate': str(t*t), 'first_coordinate_at_least_pair_floor': True,
        'both_normal_monomials_equal_one': True,
        'nonordinary_exponent_at_lambda3': str(exponents[1]),
        'ordinary_comparison_exponent': str(3*exponents[0]),
    },
    'certificate_formula': 'The exact K and I formulas in accepted WORKING-PROOF.md, with the supplied integer rows and rational constants. Seven auxiliary variables; no quantifier elimination.',
    'limits': [
        'The old analytic/per-cell bounds are inherited from the exact accepted source records, not re-executed here.',
        'The polynomial margin identities and rational coefficient inequalities are newly checked exactly.',
        'No RCF feasibility search, projected formula elimination, source simulation, source witness, or Lean proof ran.',
        'Nonattainment follows from the independently accepted all-auxiliary-state induction theorem and these constants.',
    ],
}
(here/'result.json').write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps({'status': out['status'], 'N': N, 'auxiliary_variables': 7,
    'polynomial_identities': len(identities), 'epsilon_denominator_bits': eps.denominator.bit_length(),
    'elapsed_seconds': out['elapsed_seconds']}))
