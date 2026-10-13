"""Exact transcription checks for the hand-derived cap-three collision.

No source compiler or all-cap theorem is verified by this small check.
"""
import json
import sympy as s

p, x = s.symbols("p x")
d2 = (1 - 2*p)*x + 2*p
d3 = (1 - 3*p)*x**3 + 3*p*x
d4 = (1 - 4*p + 2*p**2)*x**6 + 4*p*(1 - 2*p)*x**3 + 6*p**2*x**2
factor3 = p*(1-x)**2 * (3*x*(1-4*p) - 8*p**2*(1-x))
assert s.expand(d3-d2**3-factor3) == 0

A = 3 - 12*p + 8*p**2
branch = {x: 8*p**2/A}
pair = 2*p*(3-8*p)/A
four_defect = -1728*p**6*(4*p-1)**4*(32*p**2-32*p+9)/A**6
assert s.factor(d2.subs(branch)-pair) == 0
assert s.factor((d3-d2**3).subs(branch)) == 0
assert s.factor((d4-d2**6).subs(branch)-four_defect) == 0

print(json.dumps({
    "status": "PASS",
    "checks": ["pair-triple factor", "branch pair value", "branch triple equality", "branch fourth deficit"],
    "arithmetic": "exact rational symbolic simplification",
    "scope": "polynomial transcription only; no all-cap or formal verification"
}, indent=2))
