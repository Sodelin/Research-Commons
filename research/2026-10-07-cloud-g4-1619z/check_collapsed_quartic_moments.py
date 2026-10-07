"""Exact small moment/IFT coefficient controls, not source simulation."""
from fractions import Fraction as F
import json

import sympy as sp

d = F(1, 4)
mu1, mu2, mu3 = -F(493, 7680), F(1, 192), -F(103, 163840)
k0 = d ** 5 / 15 - d ** 6 / 90
A0 = d ** 4 * (1 - 2 * d / 5 + d ** 2 / 15)
assert (3 * mu2 - d ** 3) / 2 == 0
assert -mu3 / 6 + d ** 3 * mu1 / 6 + k0 == 0
assert d ** 3 * mu1 + 9 * k0 == -A0 / 8
variance = mu2 - mu1 ** 2
left_det = (mu1 + d) * (mu3 + d * mu2) - (mu2 + d * mu1) ** 2
right_det = mu1 * mu3 - mu2 ** 2
assert (variance, left_det, right_det) == (F(64151, 58982400), F(28781, 3774873600), F(49937, 3774873600))
alpha = (mu3 - mu1 * mu2) / variance
beta = mu2 - alpha * mu1
c = (d ** 3 - alpha ** 2 - beta) / (9 * alpha)
assert (alpha, beta, c) == (-F(17360, 64151), -F(49937, 4105664), F(1496099389, 80183617920))
assert variance > 0 and left_det > 0 and right_det > 0 and c > 0
t1, t2, t3, w1, w2, w3 = sp.symbols("t1 t2 t3 w1 w2 w3")
phi = lambda t: sp.Matrix([t, t ** 2, t ** 3])
derivative = lambda t: sp.Matrix([1, 2 * t, 3 * t ** 2])
first_det = sp.Matrix.hstack(w1 * derivative(t1), w2 * derivative(t2), phi(t1) - phi(t2)).det()
second_det = sp.Matrix.hstack(w1 * derivative(t1), w2 * derivative(t2), w3 * derivative(t3)).det()
assert sp.expand(first_det - w1 * w2 * (t1 - t2) ** 4) == 0
assert sp.expand(second_det - 6 * w1 * w2 * w3 * (t2 - t1) * (t3 - t1) * (t3 - t2)) == 0
print(json.dumps({
    "purpose": "Displayed exact moment coefficients and abstract IFT determinants only",
    "moments": [str(mu1), str(mu2), str(mu3)],
    "variance_and_localizing_determinants": [str(variance), str(left_det), str(right_det)],
    "two_node_k_over_r": str(c),
    "abstract_IFT_determinants_checked": 2,
    "actual_source_kernel_or_parameter_witness_executed": False,
    "Lean_verification": False,
    "passed": True,
}, indent=2))
