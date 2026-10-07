"""Independent bounded rational checks; no source simulation or expansion.

Input: previously preserved complete fifth coefficient JSON.
Run: python check_g4_common_scale.py PATH_TO_RESULT_JSON
"""
import hashlib
import json
import math
import sys
from fractions import Fraction as F

raw = open(sys.argv[1], 'rb').read()
expected_hash = '0a71280a0a41c3e39204f06400d4c56ba6e8e408f2f4a8015769256435646d8b'
assert hashlib.sha256(raw).hexdigest() == expected_hash
r = json.loads(raw)
indices = {}
for i, c in enumerate(r['complete_coordinates']):
    if c['shape'] == ['x'] * c['arity']:
        indices[c['arity']] = i
assert {n: indices[n] for n in (2, 3, 4, 5)} == {2: 2, 3: 5, 4: 11, 5: 21}

def phi(v):
    return F(v[indices[5]]) - 5*F(v[indices[4]]) + 10*F(v[indices[3]]) - 6*F(v[indices[2]])

assert all(phi(v) == 0 for v in r['lower_operators'].values())
H = {(x['rho_degree'], x['z_degree']): phi(x['values'])/24
     for x in r['fifth_coefficient_arrays']}
Q = {(x['rho_degree'], x['z_degree']): F(x['quotient_coefficients'][0])-5*F(x['quotient_coefficients'][1])
     for x in r['actual_source_quotient_polynomial']}
assert H == Q
stated = {
    (0, 0): F(1), (1, 0): F(-5, 2), (2, 0): F(5, 4),
    (3, 0): F(5, 6), (4, 0): F(-5, 12), (6, 0): F(-5, 24), (10, 0): F(1, 24),
    (0, 1): F(-5), (1, 1): F(10), (2, 1): F(-5, 2), (3, 1): F(-10, 3), (6, 1): F(5, 6),
    (0, 2): F(15, 2), (1, 2): F(-45, 4), (3, 2): F(15, 4),
    (0, 3): F(-10, 3), (1, 3): F(10, 3), (0, 4): F(5, 24)
}
assert H == stated

def clean(p):
    return {k: v for k, v in p.items() if v}

def add(*ps):
    out = {}
    for p in ps:
        for k, v in p.items():
            out[k] = out.get(k, F(0)) + v
    return clean(out)

def scale(p, c):
    return clean({k: v*c for k, v in p.items()})

def mul(p, q):
    out = {}
    for i, a in p.items():
        for j, b in q.items():
            out[i+j] = out.get(i+j, F(0)) + a*b
    return clean(out)

def shift(p, n):
    return {k+n: v for k, v in p.items()}

# Expand rho=1-d, z=t+d, independently using binomial coefficients.
dt = {}
for (a, b), c in H.items():
    for i in range(a+1):
        for j in range(b+1):
            key = (i+b-j, j)
            dt[key] = dt.get(key, F(0)) + c*math.comb(a,i)*(-1)**i*math.comb(b,j)
dt = clean(dt)
by_t = {j: clean({i: c for (i, k), c in dt.items() if k == j}) for j in range(5)}
assert by_t[0] == {10:F(1,24),9:F(-10,24),8:F(45,24),7:F(-100,24),6:F(85,24),5:F(-12,24)}
assert by_t[1] == {6:F(5,6),5:F(-5),4:F(5)}
assert by_t[2] == {3:F(-15,4),2:F(5,2)}
assert by_t[3] == {1:F(-5,2)}
assert by_t[4] == {0:F(5,24)}

# Derive the first moment from mean I=mean delta=mean eta=0.
k0 = {5:F(1,15),6:F(-1,90)}
A0 = {4:F(1),5:F(-2,5),6:F(1,15)}
mu1_numerator = add(scale(A0,F(-1,8)),scale(k0,F(-9)))
mu1 = {k-3:v for k,v in mu1_numerator.items()}
assert mu1 == {1:F(-1,8),2:F(-11,20),3:F(11,120)}
mu2 = {3:F(1,3)}
mu3 = add(shift(mu1,3),scale(k0,F(6)))
reduced = add(by_t[0], mul(by_t[1],mu1), mul(by_t[2],mu2), mul(by_t[3],mu3))
P = {5:F(6),4:F(-49),3:F(138),2:F(-162),1:F(78),0:F(3)}
assert reduced == scale(shift(P,5),F(1,144))

beta = [F(3),F(93,5),F(18),F(15),F(68,5),F(14)]
bernstein = {}
for k,b in enumerate(beta):
    for j in range(6-k):
        m = k+j
        bernstein[m] = bernstein.get(m,F(0)) + b*math.comb(5,k)*math.comb(5-k,j)*(-1)**j
assert clean(bernstein) == P
assert min(beta) == 3

def evalp(p, x):
    return sum((v*x**k for k,v in p.items()),F(0))

at_quarter = evalp(reduced,F(1,4))
assert at_quarter == F(7345,75497472)
print(json.dumps({
    'status': 'PASS bounded exact coefficient arithmetic only',
    'input_sha256': expected_hash,
    'input_bytes': len(raw),
    'no_merger_coordinate_indices': indices,
    'annihilated_lower_operators': list(r['lower_operators']),
    'actual_polynomial_monomials_checked': len(H),
    'complete_arrays_equal_24_times_A_minus_5B': True,
    'displayed_H_and_shifted_polynomial_checked': True,
    'forced_moment_substitution_checked': True,
    'bernstein_coefficients': [str(x) for x in beta],
    'P_lower_bound_on_unit_interval': '3',
    'constant_mean_H_at_d_one_quarter': str(at_quarter),
    'scientific_source_rerun': False,
    'parameter_search': False,
    'lean_verification': False,
    'limitation': 'Does not by itself verify lower-module applicability, actual readout transfer, or original G4.'
}, indent=2))
