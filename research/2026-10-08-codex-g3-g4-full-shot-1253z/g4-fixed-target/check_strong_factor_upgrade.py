"""Fraction-only check of the fixed-target strong-factor threshold."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json

BASE = Path(__file__).resolve().parent

def main():
    p = BASE / "NONORDINARY-BUDGET-EXACT-RECEIPT.json"
    captured = p.read_bytes()
    pin = "436619c3ca4e9312eecbeeed7cd0097475d1ea797b1fdd33d533ba6bb2e72996"
    assert sha256(captured).hexdigest() == pin
    old = json.loads(captured)
    q, b3 = F(old["pair_survival"]), F(old["three_root_survival"])
    ratio = b3/q**3
    assert ratio == F(2187, 2197)
    hazard_upper = F(old["hazard_upper_bound"])
    eta = F(1, 512)
    negative_excursion_upper = 862 * eta**2 * hazard_upper
    log_target_lower = 1-ratio
    assert negative_excursion_upper == F(431, 98304)
    assert log_target_lower == F(10, 2197) > negative_excursion_upper
    assert 10*98304-431*2197 == 36133
    assert hazard_upper/eta == F(2048, 3) < 683
    print(json.dumps({"status":"PASS", "scope":"Exact rational comparison only; source inequality remains hand proof",
                      "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
                      "authenticated_target_receipt_sha256":pin,
                      "target_normalized_triple_ratio":str(ratio),
                      "pair_hazard_upper_bound":str(hazard_upper),
                      "hypothetical_all_cell_loss_upper_bound":str(eta),
                      "negative_excursion_upper_bound":str(negative_excursion_upper),
                      "target_negative_log_ratio_lower_bound":str(log_target_lower),
                      "integer_comparison_gap":36133,
                      "necessary_some_cell_loss_strictly_greater_than":str(eta),
                      "strong_cell_count_upper_bound":682,
                      "total_cell_count_bound":None,
                      "master_closure_claim":False},indent=2)+"\n",end="")

if __name__ == "__main__":
    main()
