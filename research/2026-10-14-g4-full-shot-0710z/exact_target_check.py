"""Exact transcription check for the fixed G4 target, not a master proof.

Source formulas: FIXED-TARGET-ALL-ORDER-BODY-ELIMINATION.md, equations (1),(4).
Only the three displayed target values are checked; no source search or
finite-cap attainment is asserted.
"""
from fractions import Fraction as F
from math import comb
import json


def b(n: int, x: F, y: F, g: F) -> F:
    lam = lambda k: k * (k - 1) // 2
    return sum((F(comb(n, k)) * g**k * (1-g)**(n-k)
                * x**lam(k) * y**lam(n-k) for k in range(n+1)), F(0))


def V(z: F) -> F:
    return (2-3*z+z**3)/6


a,x,y,g,r = F(3,4),F(1,2),F(1,2),F(2,3),F(1,2)
c_body = 2*(g*g*(1-g)**2*(1-x)*(1-y)
            -g**3*(1-g)*V(x)-g*(1-g)**3*V(y))
pair=(a*r)*b(2,x,y,g)
c=a**6*r*c_body
h=a**6*(1-r)*c_body
assert pair == F(13,48)
assert c == F(-3,32768)
assert h == F(-3,32768)
print(json.dumps({
    'scope':'three exact target-value transcription controls only',
    'target':'E(3/4) B(1/2,1/2,2/3) E(1/2)',
    'b2':str(pair), 'c':str(c), 'h':str(h),
    'controls_passed':3,
    'source_existence_proved':False,
    'master_proof_complete':False,
    'lean_or_rust_execution':False
}, indent=2))
