"""Independent standard-library exact audit. No author code is executed/imported."""
import hashlib
import json
import platform
import resource
import signal
import time
from fractions import Fraction
from pathlib import Path

resource.setrlimit(resource.RLIMIT_CPU, (60, 60))
resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2, 512 * 1024**2))
signal.alarm(80)
started = time.monotonic()
HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'g3-semialgebraic-source-certificates-20261006-2156z'
PINS = {
    'WORKING-PROOF.md': '67e62d59c9cecbaf7235ce8bcf2ab807369f0a6235196aa8dbc321c50fb5b9ec',
    'providers/paired-normal-certificate.json': '2a9a8ab705c7fb689b0cbbf3d15e6972ecd71fe837c8926344bb950aa4c5a118',
    'providers/paired-normal-algebra.json': '6f47205ebfe446ab08e7a63996b59f41c3be152498a8a7d25a35bc8d17bb5317',
    'instantiation/result.json': 'a2d2c5b98cb9e8841dc954695811edc9cb998a9ecb54eebed028508394199b86',
}
for name, digest in PINS.items():
    assert hashlib.sha256((SOURCE / name).read_bytes()).hexdigest() == digest, name
old = json.loads((SOURCE / 'providers/paired-normal-certificate.json').read_text())
algebra = json.loads((SOURCE / 'providers/paired-normal-algebra.json').read_text())
instance = json.loads((SOURCE / 'instantiation/result.json').read_text())

# Sparse ring with exact Fraction coefficients. All algebra below uses this implementation.
class Poly:
    def __init__(self, terms=None, n=2):
        self.n = n
        self.t = {tuple(k): Fraction(v) for k, v in (terms or {}).items() if v}
        assert all(len(k) == n and min(k) >= 0 for k in self.t)
    def coerce(self, x):
        return x if isinstance(x, Poly) else Poly({(0,) * self.n: x}, self.n)
    def __add__(self, other):
        other = self.coerce(other)
        assert self.n == other.n
        z = dict(self.t)
        for m, c in other.t.items(): z[m] = z.get(m, 0) + c
        return Poly(z, self.n)
    __radd__ = __add__
    def __neg__(self): return Poly({m: -c for m, c in self.t.items()}, self.n)
    def __sub__(self, other): return self + (-self.coerce(other))
    def __rsub__(self, other): return self.coerce(other) - self
    def __mul__(self, other):
        other = self.coerce(other)
        assert self.n == other.n
        z = {}
        for a, c in self.t.items():
            for b, d in other.t.items():
                m = tuple(x + y for x, y in zip(a, b))
                z[m] = z.get(m, 0) + c*d
        return Poly(z, self.n)
    __rmul__ = __mul__
    def __pow__(self, k):
        assert isinstance(k, int) and k >= 0
        z, a = self.coerce(1), self
        while k:
            if k & 1: z = z*a
            k //= 2
            if k: a = a*a
        return z
    def __eq__(self, other): return self.t == self.coerce(other).t
    def diff(self, axis):
        z = {}
        for m, c in self.t.items():
            if m[axis]:
                new = list(m); new[axis] -= 1
                z[tuple(new)] = c*m[axis]
        return Poly(z, self.n)
    def eval_axis(self, axis, value):
        z = {}
        for m, c in self.t.items():
            new = list(m); new[axis] = 0; new = tuple(new)
            z[new] = z.get(new, 0) + c*value**m[axis]
        return Poly(z, self.n)
    def stretch(self, axis, k):
        z = {}
        for m, c in self.t.items():
            new = list(m); new[axis] *= k; z[tuple(new)] = c
        return Poly(z, self.n)
    def div_q(self, divisor):
        assert self.n == divisor.n == 2
        assert all(m[0] == 0 for m in self.t) and all(m[0] == 0 for m in divisor.t)
        remain, quotient = self, Poly()
        lead = max(divisor.t, key=lambda x: x[1]); degree = lead[1]
        while remain.t and max(m[1] for m in remain.t) >= degree:
            key = max(remain.t, key=lambda x: x[1])
            term = Poly({(0, key[1]-degree): remain.t[key]/divisor.t[lead]})
            quotient = quotient + term
            remain = remain - term*divisor
        return quotient, remain
    def l1(self): return sum(abs(c) for c in self.t.values())

def variable(axis, n=2):
    m = [0]*n; m[axis] = 1
    return Poly({tuple(m): 1}, n)

def product(values):
    ans = Poly({(0, 0): 1})
    for v in values: ans = ans*v
    return ans

def scalar(poly):
    assert all(not any(k) for k in poly.t)
    return poly.t.get((0,)*poly.n, Fraction(0))

p, q = variable(0), variable(1)
ls = [1, 3, 6, 10, 15, 21]
r = Fraction(1, 2)
ROWS = {
    'F0': [15183, -25713, 22646, -7392, 0, 0],
    'F1': [6548201697807, -44625849584225, 322432296415950,
           -1841737514410080, 2686046822645760, -1127647220334592],
}
polys, scales, curvature_data = {}, {}, {}
for label, row in ROWS.items():
    assert row == instance['integer_normal_rows'][label]
    scale = sum(row)
    assert scale > 0 and scale == instance['positive_normal_scales'][label]
    scales[label] = scale
    pairs = [(n, c) for n, c in zip(ls, row) if c]
    rec = old['normal_records'][label]
    assert [n for n, _ in pairs] == rec['exponents'] == algebra[label]['exponents']
    assert [Fraction(c, scale) for _, c in pairs] == list(map(Fraction, rec['c']))
    assert list(map(Fraction, rec['c'])) == list(map(Fraction, algebra[label]['c']))
    assert sum(c*n for n, c in pairs) == 0
    assert sum(c*(1-r**n)/(1-r) for n, c in pairs) == 0
    F = sum(c*(1-q**n) for n, c in pairs)
    polys[label] = F
    neutral = (q-1)**2 * (2*q-1)**2
    if label == 'F1': neutral = neutral*(4*q-1)**2
    quotient, remainder = F.div_q(neutral)
    assert remainder == 0
    descending = [quotient.t.get((0, j), Fraction(0))
                  for j in range(max(k[1] for k in quotient.t), -1, -1)]
    assert all(c > 0 for c in descending)
    assert descending == [scale*Fraction(v) for v in rec['positive_quotient_coefficients']]
    assert scalar(quotient.eval_axis(1, 0)) == scale
    assert Fraction(rec['coefficient_L1']) == Fraction(sum(abs(c) for c in row), scale)

    # Independent route: L_q = J / D, then L_qq = (J_q D - J D_q) / D^2.
    factors = [1+p*(q**n-1) for n, _ in pairs]
    D = product(factors)
    J = sum(-c*f.diff(1)*product(factors[:i] + factors[i+1:])
            for i, ((n, c), f) in enumerate(zip(pairs, factors)))
    raw = J.diff(1)*D-J*D.diff(1)
    assert not any(a == 0 for a, b in raw.t)
    max_p = max(a for a, b in raw.t)
    max_q = max(b for a, b in raw.t)
    terms = {}
    for bpow in range(max_q+1):
        previous = Fraction(0)
        for apow in range(1, max_p+1):
            current = raw.t.get((apow, bpow), 0)+previous
            if current: terms[(apow-1, bpow)] = current
            previous = current
        assert previous == 0
    numerator = Poly(terms)
    assert raw == p*(1-p)*numerator
    expected = Poly({tuple(m): scale*Fraction(v) for m, v in rec['normalized_Lqq_numerator_terms']})
    assert numerator == expected
    fpp = scalar(F.diff(1).diff(1).eval_axis(1, 1))
    assert fpp > 0 and numerator.eval_axis(1, 1) == fpp
    Mq = numerator.diff(1).l1()
    assert Mq > 0
    assert Fraction(fpp, scale) == Fraction(rec['F_second_derivative_at_one'])
    assert Mq/scale == Fraction(rec['normalized_Lqq_numerator_q_derivative_L1_bound'])
    width = min(Fraction(1, 8), fpp/(2*Mq))
    assert width == Fraction(rec['near_one_width'])
    curvature_data[label] = {'term_count': len(numerator.t), 'width': str(width),
                             'at_one': str(fpp), 'derivative_l1': str(Mq)}

# Reconstruct the historical constants from the independently obtained polynomials.
c = {k: Fraction(v) for k, v in old['constants'].items()}
F1 = polys['F1'] * Fraction(1, scales['F1'])
T12 = 2*F1-F1.stretch(1, 2)
T12q, T12rem = T12.div_q((q-r)**2)
assert T12rem == 0
D12 = T12q.l1()
T13 = 3*F1-3*F1.stretch(1, 2)+F1.stretch(1, 3)
Kr = scalar(T13.eval_axis(1, r))
assert Kr == scalar(F1.eval_axis(1, r**3)) and Kr > 0
MK = T13.diff(1).l1()
eta = min(Fraction(1, 32), Kr/(2*MK))
width = min(Fraction(v['width']) for v in curvature_data.values())
A = 4*Fraction(15, 32)**2*Fraction(7, 8)**2
Vmin = 4*Fraction(23, 32)**2*Fraction(7, 32)**2
B0 = Fraction(sum(abs(z) for z in ROWS['F0']), scales['F0'])
B1 = Fraction(sum(abs(z) for z in ROWS['F1']), scales['F1'])
K = Kr/2
outside0 = 4*width**2*eta**2
outside1 = 64*width**2*eta**4
p0 = min(Fraction(1, 2), A/D12, K/(3*B1), Vmin/(2*B0),
         outside0/(2*B0), outside1/(2*B1))
delta, gamma = Vmin/2, K/6
rebuilt = {
    'near_one_width': width, 'Q': 1-width, 'root_interval_half_width': eta,
    'A': A, 'T12_divided_square_coefficient_L1': D12, 'T13_at_r': Kr,
    'T13_derivative_L1': MK, 'K_lower_bound': K, 'B0': B0, 'B1': B1,
    'V_F0_lower_bound': Vmin, 'outside_U_F0_lower_bound': outside0,
    'outside_UV_F1_lower_bound': outside1, 'p0': p0, 'delta': delta,
    'gamma': gamma,
    'C_star': min(p0*width, gamma*Fraction(15, 32)/(2*B1*(B0/delta)**2)),
}
assert rebuilt == c
assert min(rebuilt.values()) > 0
U, V = [r-eta, r+eta], [r*r-eta, r*r+eta]
assert 0 < V[0] < V[1] < U[0] < U[1] < 1-width < 1
assert [str(z) for z in U] == instance['root_intervals']['U']
assert [str(z) for z in V] == instance['root_intervals']['V']
alpha, beta = 1-U[1], 1-V[1]
B0 *= scales['F0']; delta *= scales['F0']
B1 *= scales['F1']; gamma *= scales['F1']
eps = min(p0*width/2, alpha/(4*B0), beta/(4*B1),
          gamma*alpha*delta**2/(16*B1*B0**2), Fraction(1, 4))
b = 1/(1+eps)
rebuilt_instance = dict(alpha=alpha, beta=beta, B0=B0, B1=B1,
                        delta=delta, gamma=gamma, epsilon=eps, pair_floor_b=b)
assert rebuilt_instance == {k: Fraction(v) for k, v in instance['constants'].items()}
assert 0 < eps < p0*width
assert B0*eps/alpha < Fraction(1, 2) and B1*eps/beta < Fraction(1, 2)
assert 8*B1*B0**2*eps < gamma*alpha*delta**2

# Universal transition identities in a separate twelve-variable sparse ring.
B, d, P, Q, T, V1, V2, p, b0, b1, de, ga = [variable(i, 12) for i in range(12)]
identities = {
    'pair_budget': ((1+B)-(1-d)*(1+B+d), d*B+d*d),
    'first_U': ((1-b0*Q)*(1-b0*p*p)-(1-b0*(Q+p*p)), b0*b0*Q*p*p),
    'first_V': ((1+de*V1)*(1+de*p)-(1+de*(V1+p)), de*de*V1*p),
    'second_U': ((1+ga*T)*(1+ga*p**3)-(1+ga*(T+p**3)), ga*ga*T*p**3),
    'second_V': ((1-b1*V2)*(1-b1*p*p)-(1-b1*(V2+p*p)), b1*b1*V2*p*p),
    'cauchy_squares': ((P*p*p+T)**2-4*Q*Q*p*p,
                       (P*p*p-T)**2+4*p*p*(P*T-Q*Q)),
    'cauchy_update': ((P+p)*(T+p**3)-(Q+p*p)**2,
                      P*T-Q*Q+p*(P*p*p+T-2*Q*p)),
    'V_square': ((V1+p)**2-(V2+p*p), V1*V1-V2+2*V1*p),
}
for label, (left, right) in identities.items(): assert left == right, label

# Original target identity, with no search and no approximate logarithms.
N = 175
t = 1-Fraction(1, 2**N)
exponents = [Fraction(n+2)-Fraction(1, 2**(n-1)) for n in ls]
assert t*t >= b
assert (1-Fraction(1, 2**174))**2 < b
assert str(t) == instance['target']['base']
assert old['algebraic_input']['N'] == N == instance['target']['N']
assert int(old['algebraic_input']['b_numerator']) == t.numerator
assert int(old['algebraic_input']['b_denominator']) == t.denominator
for row in ROWS.values(): assert sum(c*e for c, e in zip(row, exponents)) == 0
assert exponents[1] == Fraction(19, 4) < 3*exponents[0] == 6
assert all(e > 0 for e in exponents) and 0 < t < 1

out = {
    'status': 'PASS independent standard-library exact audit',
    'python': platform.python_version(),
    'elapsed_seconds': time.monotonic()-started,
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'input_sha256': PINS,
    'method': 'Sparse exact Fraction ring; common-denominator first-log-derivative differentiation; no author scripts or SymPy imported.',
    'endpoint_numerators': curvature_data,
    'historical_constants_reconstructed': len(rebuilt),
    'new_constants_reconstructed': {k: str(v) for k, v in rebuilt_instance.items()},
    'eight_margin_identities': list(identities),
    'target': {'N': N, 'same_old_target': True, 't_squared_ge_floor': True,
               'N174_fails_this_floor': True, 'both_normal_exponent_sums_zero': True,
               'lambda3_exponent': str(exponents[1]), 'ordinary_exponent': '6'},
    'limits': ['No RCF/QE solver, global log inequality solver, Lean or source compiler was run.',
               'Analytic integration/remainder reasoning, induction and source-fibre soundness are hand-audited separately.',
               'No new NO family or universal certificate-completeness claim.'],
}
(HERE/'result.json').write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps({'status': out['status'], 'elapsed_seconds': out['elapsed_seconds'],
                  'endpoint_term_counts': {k: v['term_count'] for k, v in curvature_data.items()},
                  'historical_constants_reconstructed': len(rebuilt),
                  'margin_identities': len(identities), 'target_N': N}))
