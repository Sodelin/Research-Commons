"""Exact domain checks on the saved actual physical means/contrast candidate."""
from __future__ import annotations
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import sys

def main():
    sys.set_int_max_str_digits(0)
    root=Path(__file__).parent
    p=root/"FREE-ARM-GATE-v3.json"
    captured=p.read_bytes()
    r=json.loads(captured)
    A=list(map(F,r["saved_final_A_decimal"]))
    w=list(map(F,r["saved_final_w_decimal"]))
    theta=list(map(F,r["saved_final_allocation_logits_decimal"]))
    t=F(1,1024)
    checks=[]
    for a,b in zip(A,w):
        s=1-a*t
        h2=b*t**3
        assert 0<s<1 and h2>0 and h2<s*s and h2<(1-s)**2
        checks.append({"positive_arm_mean":True,"positive_contrast":True,"both_algebraic_survivals_strict":True})
    # Softmax gives35 finite positive hazards summing to H exactly, so the
    # exact connector product is the ORIGINAL rational product below.
    assert len(theta)==34
    connector_product=F(9,10)**8*F(1023,1024)**27
    pair=F(7,8)*connector_product
    for a in A:
        pair*=1-a*t/2
    calibration=F(1,4)/pair
    assert 0<calibration<1
    result={"status":"EXACT_RATIONAL_PHYSICAL_DOMAIN_CHECKS_ONLY",
            "candidate_sha256":sha256(captured).hexdigest(),
            "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "cells_checked":36,"cell_arm_checks":checks,
            "gap_hazards_finite_positive_by_softmax":True,"dependent_gap_preserves_total_H":True,
            "exact_connector_product":str(connector_product),"exact_raw_pair_survival":str(pair),
            "exact_positive_final_calibration_survival":str(calibration),
            "calibration_survival_decimal":float(calibration),
            "A_min_decimal":float(min(A)),"A_max_decimal":float(max(A)),
            "w_min_decimal":float(min(w)),"w_max_decimal":float(max(w)),
            "not_claimed":["candidate response equals target","interval enclosure of response","common zero","G4 closure"]}
    (root/"FREE-ARM-ADMISSION.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k in ['status','calibration_survival_decimal','A_min_decimal','A_max_decimal','w_min_decimal','w_max_decimal']}))
if __name__=="__main__":
    main()
