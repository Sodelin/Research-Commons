"""Small exact polynomial controls for displayed hand algebra.

No source kernel, genealogy compiler, scan, numerical witness or Lean is run.
The generic four-site summation check has abstract variables and does not
assert that independently assigned coefficients are actual-source controls.
"""
import json
from fractions import Fraction

import sympy as sp

d, z = sp.symbols("d z")
rho = 1 - d
eta = (3 * (z - d) ** 2 - d ** 3) / 2
K = sp.Rational(1, 18) - rho / 10 + rho ** 3 / 18 - rho ** 6 / 90
delta = K + z ** 3 / 3 - d * z ** 2 / 2 - z * eta / 3
I = -32 * z ** 3 + 48 * d * z ** 2 - 16 * d ** 3 + 15 * d ** 4 - 6 * d ** 5 + d ** 6 + 24 * z * eta
A = d ** 4 * (1 - 2 * d / 5 + d ** 2 / 15)
P3 = (3 * d ** 2 - d ** 3) / 2
e_table = (-3 * z ** 3 + 2 * z * P3 + 3 * d * z ** 2 - 18 * K) / 6
identities = {
    "ordinary_K_polynomial": K - (d ** 3 / 6 - d ** 4 / 6 + d ** 5 / 15 - d ** 6 / 90),
    "actual_source_quartic_coupling": I + 96 * delta + A + 8 * z * eta,
    "displayed_e_table_reduction": e_table + sp.Rational(2, 3) * z * eta + 3 * delta,
}

r0, r1, r2 = sp.symbols("r0 r1 r2")
gaps = sp.symbols("gap0:3")
ks = sp.symbols("k0:4")
rs = [r0, r1, r2, -r0 - r1 - r2]
positions = [sum(gaps[:j]) for j in range(4)]
prefixes = [sum(rs[:j]) for j in range(5)]
pair_sum = sum(rs[j] * rs[k] * (positions[k] - positions[j]) for j in range(4) for k in range(j + 1, 4))
area_sum = -sum(gaps[j] * prefixes[j + 1] ** 2 for j in range(3))
quartic_pairs = sum(rs[j] * ks[k] for j in range(4) for k in range(j + 1, 4))
quartic_prefix = sum(prefixes[j] * ks[j] for j in range(4))
identities["four_site_clock_summation_by_parts"] = pair_sum - area_sum
identities["four_site_quartic_prefix_rewrite"] = quartic_pairs - quartic_prefix
controls = {name: str(sp.expand(expr)) for name, expr in identities.items()}
assert all(value == "0" for value in controls.values())
clock_factor = Fraction(15, 2) * Fraction(-2, 15) * 6 * Fraction(-2, 9)
own_clock_factor = Fraction(15, 2) * Fraction(-2, 15) * 2 * Fraction(-2, 3)
quartic_factor = Fraction(15, 2) * Fraction(-2, 15) * 2 * (-3)
assert (clock_factor, own_clock_factor, quartic_factor) == (Fraction(4, 3), Fraction(4, 3), Fraction(6))
print(json.dumps({
    "purpose": "Exact displayed polynomial/arithmetic controls only",
    "identities": controls,
    "clock_and_own_clock_factors": [str(clock_factor), str(own_clock_factor)],
    "quartic_area_factor": str(quartic_factor),
    "actual_source_kernel_evaluated": False,
    "independent_source_parameters_assumed": False,
    "Lean_verification": False,
    "passed": True,
}, indent=2))
