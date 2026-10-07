"""Displayed source-polynomial and rational positivity controls only."""
from fractions import Fraction as F
import json
import sympy as sp

d, t, u = sp.symbols("d t u")
eta = (3 * t ** 2 - d ** 3) / 2
delta = -t ** 3 / 6 + d ** 3 * t / 6 + d ** 5 / 15 - d ** 6 / 90
A = d ** 4 * (1 - 2 * d / 5 + d ** 2 / 15)
physical_F = A + 8 * (d + t) * eta + 54 * delta
shown_F = 3 * t ** 3 + 12 * d * t ** 2 + 5 * d ** 3 * t - 3 * d ** 4 + sp.Rational(16, 5) * d ** 5 - sp.Rational(8, 15) * d ** 6
P = 5 - 30 * u + 48 * u ** 2 - 24 * u ** 4
assert sp.expand(physical_F - shown_F) == 0
assert sp.expand(shown_F.subs({t: -3 * u ** 3, d: 3 * u ** 2}) - (3 * u ** 2) ** 4 * P / 5) == 0
assert P.subs(u, sp.Rational(1, 3)) == sp.Rational(1, 27)
assert sp.diff(P, u).subs(u, sp.Rational(1, 3)) == -sp.Rational(14, 9)
assert sp.diff(P, u, 2).subs(u, sp.Rational(2, 5)) == sp.Rational(1248, 25)
assert P.subs(u, sp.Rational(2, 5)) == sp.Rational(41, 625)
assert sp.diff(P, u).subs(u, sp.Rational(2, 5)) == sp.Rational(282, 125)
lower = F(1, 27) - F(4900, 202176)
assert lower == F(647, 50544) and lower > 0
assert F(54, 8) == F(27, 4)
R, S = sp.symbols("R S")
assert sp.expand(3 * R * (R + S) - 2 * (R ** 2 + R * S + S ** 2) - (R - S) * (R + 2 * S)) == 0
print(json.dumps({
    "purpose": "Displayed polynomial reductions and rational certificate constants only",
    "F_and_endpoint_polynomial_identities_passed": True,
    "middle_interval_positive_lower_bound": str(lower),
    "asymmetric_difference_factorization_passed": True,
    "actual_source_kernel_or_witness_executed": False,
    "Lean_verification": False,
    "passed": True,
}, indent=2))
