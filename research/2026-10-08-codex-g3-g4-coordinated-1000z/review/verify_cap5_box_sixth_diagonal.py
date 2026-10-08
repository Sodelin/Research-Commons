"""Independent Fraction interval of actual fair-cell no-merger diagonal."""
from fractions import Fraction as F
from pathlib import Path
from math import comb
import datetime
import hashlib
import json
import sys

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[3]
P = ROOT / "research/2026-10-08-codex-g3-g4-coordinated-1000z"

class I:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = self.lo if hi is None else F(hi)
        assert self.lo <= self.hi
    def __add__(self, other):
        o = other if isinstance(other, I) else I(other)
        return I(self.lo + o.lo, self.hi + o.hi)
    __radd__ = __add__
    def __neg__(self):
        return I(-self.hi, -self.lo)
    def __sub__(self, other):
        return self + -(other if isinstance(other, I) else I(other))
    def __rsub__(self, other):
        return I(other) - self
    def __mul__(self, other):
        o = other if isinstance(other, I) else I(other)
        values = [x*y for x in [self.lo, self.hi] for y in [o.lo, o.hi]]
        return I(min(values), max(values))
    __rmul__ = __mul__
    def __truediv__(self, other):
        o = other if isinstance(other, I) else I(other)
        assert not o.lo <= 0 <= o.hi
        return self * I(1/o.hi, 1/o.lo)
    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0 and self.lo >= 0
        return I(self.lo**n, self.hi**n)
    def encoded(self):
        return [str(self.lo), str(self.hi)]

def capture(path):
    raw = path.read_bytes()
    return json.loads(raw), hashlib.sha256(raw).hexdigest()

doc, input_sha = capture(P / "g4-positive/library-centre/RATIONAL-BOX-INPUT.json")
receipt, result_sha = capture(P / "g4-forest/CAP6-FROM-CAP5-BOX-v2.json")
assert input_sha == "bb6bcc498125a86b797748f8f936b60051ac327f07d761fab2caeab531d70a8e"
assert result_sha == "9605a587604bfde5e21fd783d9170702298cef27b080d57aca152e8333b3866f"
fixed = doc["fixed_rational_source"]
t, d = F(fixed["t"]), F(fixed["d"])
radius = F(doc["parameter_cube_radius"])
weights = [I(F(x)-radius, F(x)+radius) for x in doc["approximate_rational_parameters"][:3]] + [I(fixed["w4"])]
means = list(map(F, fixed["means"]))
answer = I(1)
cells = []
for A, W in zip(means, weights):
    s = I(1-A*t)
    h2 = W*t**3
    xy = s*s-h2
    assert h2.lo > 0 and h2.hi < min(s.lo**2, (1-s.lo)**2)
    # The actual independent half-coin law sums all labelled routing masks:
    # 2^-6 sum_k C(6,k) x^C(k,2) y^C(6-k,2).
    # Pair complementary k terms, so no square-root enclosure is needed.
    b6 = I(0)
    for k in range(4):
        px = k*(k-1)//2
        py = (6-k)*(5-k)//2
        low, high = min(px, py), max(px, py)
        diff = high-low
        if k == 3:
            term = xy**low
        else:
            term = 2*xy**low*sum((comb(diff, 2*j)*s**(diff-2*j)*h2**j for j in range(diff//2+1)), I(0))
        b6 += comb(6,k)*term/64
    q = F(1)-A*t/2
    answer *= (b6/q**15)**2
    cells.append({"b6_actual_mask_sum_interval":b6.encoded(), "pair_survival":str(q)})
residual = d**15*(answer-I(1))
assert residual.hi < 0
saved = list(map(F, receipt["new_diagonal_difference_tight_interval"]))
assert max(residual.lo, saved[0]) <= min(residual.hi, saved[1])
assert all(F(a)<F(b) and (F(b)<0 or F(a)>0) for a,b in receipt["full20_cap6_cube_residual_intervals"])
assert receipt["cap6_nine_cube_residual_intervals"] == [receipt["full20_cap6_cube_residual_intervals"][i] for i in receipt["cap6_target_free_coordinate_indices"]]
for a,b in receipt["ordinary_edge_survival_cube_intervals"]:
    assert 0 < F(a) <= F(b) < 1
for cell in receipt["arm_inequality_cube_intervals"]:
    assert all(F(a)>0 and F(a)<=F(b) for a,b in cell)
    assert F(cell[1][1]) < 1
direct = list(map(F, receipt["full20_cap6_cube_residual_intervals"][0]))
assert max(direct[0], saved[0]) <= min(direct[1], saved[1])
record = {"schema":"independent-exact-Fraction-sixth-diagonal-cube-v1", "utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "input_sha256":input_sha, "receipt_sha256":result_sha, "cells":cells,
          "independent_rational_diagonal_residual_interval":residual.encoded(), "independent_upper_endpoint_negative":True,
          "saved_tight_interval_overlaps_independent_exact_interval":True,
          "all20_saved_residual_intervals_separate_zero":True,"nine_saved_coordinates_match_complete_rows":True,
          "all_saved_physical_gate_intervals_strict":True,"direct_and_telescoped_saved_diagonals_overlap":True,
          "author_inherited_or_mpmath_executions":0,
          "scope":"Actual fair independent six-root mask diagonal plus exact edge telescoping independently certified for entire rational cube; remaining full-row interval computation source reviewed and receipt authenticated separately."}
(P / "review/G4-CAP5-BOX-SIXTH-DIAGONAL-STATIC-VERIFICATION.json").write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps({"status":"PASS","independent_diagonal_interval":[float(residual.lo),float(residual.hi)],"all20_saved_intervals_separate":True}))
