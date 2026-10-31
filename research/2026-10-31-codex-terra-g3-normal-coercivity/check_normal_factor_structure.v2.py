"""Corrected factor selection; check the held cap8 normal, no bank/grid."""
import hashlib
import json
from pathlib import Path
import sympy as s

import argparse
parser = argparse.ArgumentParser(description="Check the pinned existing cap8 normal factors.")
parser.add_argument("normal_json", type=Path)
source = parser.parse_args().normal_json
raw = source.read_bytes()
assert hashlib.sha256(raw).hexdigest() == "2844871e9c48a810df35670da4b5eb1f8c02c564d0c5bf3a13e43c141c097a3a"
data = json.loads(raw)
print('normal body SHA256', hashlib.sha256(raw).hexdigest(), flush=True)
q, x, beta = s.symbols('q x beta')
expr = s.sympify(data['source_function'], locals={'q':q,'x':x,'beta':beta})
args = s.Mul.make_args(expr)
core = max((item for item in args if item.is_Add), key=lambda item: len(item.args))
outside = s.Mul(*(item for item in args if item is not core))
assert s.simplify(outside-q**2*(beta-1)*(q-1)**2/187342848) == 0
pol = s.Poly(core, beta)
assert pol.degree() == 3
print('PASS exact (1-beta)(1-q)^2 factor and cubic remainder core', flush=True)
for k in (2,3):
    coeff = pol.coeff_monomial(beta**k)
    at_q1 = s.Poly(coeff.subs(q,1),x)
    deriv_corner = s.diff(coeff,q).subs({q:1,x:1})
    print('beta degree', k, 'coefficient at q=1 identically zero:', at_q1.is_zero,
          'q-derivative at (1,1):', deriv_corner, flush=True)
    assert at_q1.is_zero and deriv_corner == 0
print('PASS beta^2 remainder has extra (1-q) and vanishes after division at (q,x)=(1,1)', flush=True)
