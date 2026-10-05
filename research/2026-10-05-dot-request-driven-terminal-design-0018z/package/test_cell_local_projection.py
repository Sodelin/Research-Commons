#!/usr/bin/env python3
"""A word can fail globally while its selected source-history branch is valid."""
import json
from pathlib import Path
from compile_projected_word import compile_policy
from provider_models import models
from project_branch_word import project_branch_word
from verify_policy import verify
ROOT=Path(__file__).resolve().parent
def run():
    prefix=[{'support':[0],'weights':['1','0']}]
    menu=[[0],[1],[0,1]];sites=[['H0'],['H0']];budget=[2,2,1]
    rows=[]
    for name,weight in [('low_history_cell','3*h0_0'),('high_history_cell','(3*h0_0-1)/2')]:
        call={'support':[0,1],'weights':[weight,'1-('+weight+')']}
        # The old global-word gate MUST fail: this action is not legal at
        # some genuine sources that belong to the OTHER history cell.
        old=compile_policy(models(),prefix+[call],menu,sites,budget)
        assert old['status']=='UNKNOWN_OR_REFUTED_PROJECTED_CANDIDATE',old['status']
        projected=project_branch_word(models(),prefix+[call],menu,sites,budget)
        assert projected['status']=='COMPLETE_AFFINE_LEGAL_WORD_TARGET_REGIONS_PROJECTED'
        assert projected['whole_word_globally_verified'] is False
        rows.append({'name':name,'unconditional_word_status':old['status'],'unconditional_source_gate':old['verification']['status'],
                     'legal_history_projection_status':projected['status'],'not_a_whole_policy_certificate':True})
    delivered=json.loads((ROOT/'CAD-ASSEMBLED-POLICY-RECEIPT.json').read_text())
    assert delivered['verification']['status']=='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND'
    assert len(delivered['verification']['receipts'])==468
    out={'status':'PASS_CELL_LOCAL_TARGET_PROJECTION_AND_GLOBAL_POLICY_DISTINCTION','controls':rows,
         'final_multibranch_source_gate':'FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND','source_parameters_shared':True,
         'trust':'Same-backend source gate; legal-word projection is separate from whole-policy proof'}
    (ROOT/'CELL-LOCAL-PROJECTION-CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'cell_local_word_controls':len(rows)}))
if __name__=='__main__':run()
