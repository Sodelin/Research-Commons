"""Exact Fraction-only countercontrol; no original source module execution."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json

BASE = Path(__file__).resolve().parent
PROVIDER = "NONORDINARY-BUDGET-EXACT-RECEIPT.json"
PIN = "436619c3ca4e9312eecbeeed7cd0097475d1ea797b1fdd33d533ba6bb2e72996"

def main():
    data = (BASE / PROVIDER).read_bytes()
    assert sha256(data).hexdigest() == PIN
    provider = json.loads(data)
    assert provider["status"] == "PASS"
    a, r = F(3, 4), F(1, 2)
    b2_body, b3_body = F(13, 18), F(3, 8)
    q_target = a * b2_body * r
    b3_target = a**3 * b3_body * r**3
    assert q_target == F(provider["pair_survival"])
    assert b3_target == F(provider["three_root_survival"])
    rows = []
    for n in (4, 8, 16):
        x, s = 1 - F(1, n*n), 1 - F(1, n*n*n)
        beta = (1+x)/2
        q_prefix = s**(n+1) * beta**n
        lower = 1 - F(n+1, n**3) - F(1, 2*n)
        leading = a/q_prefix
        b3_weak = x**3/4 + 3*x/4
        assert b3_weak - beta**3 == -F(1, 8*n**6)
        assert 0 < x < 1 and 0 < s < 1 and 0 < beta < 1
        assert q_prefix >= lower >= F(51, 64) > a
        assert 0 < leading < 1
        assert leading * q_prefix * b2_body * r == q_target
        b3_prefix = s**(3*(n+1)) * b3_weak**n
        b3_word = leading**3 * b3_prefix * b3_body * r**3
        b3_formula = b3_target * (1-F(1, 8*n**6*beta**3))**n
        assert b3_word == b3_formula < b3_target
        # Complete row TV identity for equal pair survival, separately shown
        # coordinate-by-coordinate in the authenticated target receipt.
        tv3 = F(3, 2) * (b3_target-b3_word)
        assert tv3 > 0
        # This is the ordinary survival of the exact substituted skeleton.
        assert leading * q_prefix == a
        rows.append({"N": n, "weak_cell_count": n, "total_bigon_count": n+1,
                     "weak_arm_survival": str(x), "positive_gap_survival": str(s),
                     "weak_pair_survival": str(beta), "prefix_pair_survival": str(q_prefix),
                     "leading_survival": str(leading), "word_pair_survival": str(q_target),
                     "word_three_root_survival": str(b3_word),
                     "exact_full_cap_three_tv": str(tv3),
                     "strong_skeleton_exact_target_all_arities": True,
                     "full_cap_three_target_agreement": False})
    print(json.dumps({"status":"PASS", "scope":"Exact failed-inference countercontrol only",
                      "executed_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
                      "provider_receipt":{"path":PROVIDER,"sha256":PIN},
                      "inherited_source_module_executed":False,
                      "exact_prefix_replica_claim":False,"rows":rows}, indent=2)+"\n",end="")

if __name__ == "__main__":
    main()
