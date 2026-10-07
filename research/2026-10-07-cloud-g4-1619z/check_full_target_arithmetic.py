"""Exact rational coefficient controls; no source simulation or theorem prover."""
from fractions import Fraction as F
import json

row4, row3 = F(29, 45), -F(20, 9)
w_coefficient = row4 * 1080 + row3 * 270
i_coefficient = row4 * 5 + row3
h_coefficient = -F(2, 9) * 135 + 18
assert (w_coefficient, i_coefficient, h_coefficient) == (F(96), F(1), F(-12))
print(json.dumps({
    "purpose": "Exact rational coefficient controls for hand proof; no source evaluation",
    "J_W_coefficient": str(w_coefficient),
    "J_I_coefficient": str(i_coefficient),
    "same_f_zero_h_W_coefficient": str(h_coefficient),
    "source_scan": False,
    "Lean_verification": False,
    "passed": True,
}, indent=2))
