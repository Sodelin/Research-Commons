"""Exact scalar algebra checks; not a genealogy simulator or G4 certificate."""
import json
from fractions import Fraction as F
import sympy as s

x, y, g = s.symbols("x y g")
h = 1-g
d2 = g*g*x+h*h*y+2*g*h
d3 = g**3*x**3+h**3*y**3+3*g*g*h*x+3*g*h*h*y
star = g*(g*x+h)**2+h*(g+h*y)**2
assert s.expand((d2+d3)/2-star-(g**3*x*(1-x)**2+h**3*y*(1-y)**2)/2) == 0
assert s.expand(star-d2*d2-g*h*(g*(1-x)-h*(1-y))**2) == 0

v1,v2,w1,w2 = s.symbols("v1 v2 w1 w2")
envelope = lambda r,t: (t+3*r-1)/3
defect = envelope(1+v1,1+w1)*envelope(1+v2,1+w2)-envelope((1+v1)*(1+v2),(1+w1)*(1+w2))
assert s.expand(defect-(3*v1*w2+3*v2*w1-2*w1*w2)/9) == 0

def row(cells):
    r = triple = fourth = F(1)
    for q,p in cells:
        yi = 1/q
        r *= 1+2*p*(yi-1)
        triple *= 1+3*p*(yi*yi-1)
        fourth *= 1+4*p*(1-2*p)*(yi**3-1)+6*p*p*(yi**4-1)
    v,w = r-1,triple-1
    u = 2*w/(3*v)-2
    target_q,target_p = 1/(1+u),v/(2*u)
    f4 = (9*v**3-12*v*v*w+18*v*v+6*v*w*w-12*v*w+9*v+8*w*w)/(9*v)
    assert F(1,100) < target_q < 1
    assert 0 < target_p <= F(1,4)
    return target_q,target_p,fourth-f4

positive = row([(F(1,5),F(1,100)),(F(1,5),F(1,100))])
negative = row([(F(1,5),F(1,5)),(F(1,5),F(1,4))])
assert positive == (F(13,89),F(169,11875),F(88959456,5078125))
assert negative == (F(17,469),F(289,2260),F(-1010304,425))
print(json.dumps({
    "status": "PASS",
    "scope": "three polynomial identities and two rational residual controls only",
    "positive_control": [str(v) for v in positive],
    "negative_control": [str(v) for v in negative],
    "source_simulation": False,
    "lean_verification": False,
    "g4_certificate": False,
}, indent=2))
