#!/usr/bin/env python3
"""A history-dependent algebraic action in the SAME admitted source image."""
import copy
import json
from pathlib import Path
from provider_models import models,policy
from verify_algebraic_policy import verify
from section_point import select
import sympy as sp
import z3

ROOT=Path(__file__).resolve().parent
def main():
    p=policy();node=p['next'];node['sections']=[{'name':'action_root_weight','coefficients':['-h0_0','0','1'],'lower':'0','upper':'1'}]
    node['weights']=['action_root_weight','1-action_root_weight']
    out=verify(models(),p,[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1])
    assert out['status']=='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND',out
    (ROOT/'ALGEBRAIC-POLICY.json').write_text(json.dumps(p,indent=2)+'\n');(ROOT/'ALGEBRAIC-POLICY-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
    controls=[]
    encoded,value=select(node['sections'][0],{'h0_0':z3.RealVal('2/3')})
    assert sp.simplify(value*value-sp.Rational(2,3))==0 and value.is_Rational is False
    (ROOT/'EXACT-SECTION-POINT.json').write_text(json.dumps({'input_first_coordinate':'2/3','exact_action_root':encoded,'root_equation_checked_exactly':True},indent=2)+'\n')
    for name,coefficients,lower,upper in [('no_root',['h0_0','0','1'],'0','1'),
                                          ('nonunique_interval',['-3/32','11/16','-3/2','1'],'0','1'),
                                          ('hidden_source_coefficient',['-sameOriginalSurvival0','0','1'],'0','1'),
                                          ('future_response_coefficient',['-h1_0','0','1'],'0','1')]:
        bad=copy.deepcopy(p);bad['next']['sections'][0].update(coefficients=coefficients,lower=lower,upper=upper)
        checked=verify(models(),bad,[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1]);assert checked['status']!='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND';controls.append({'name':name,'result':checked})
    (ROOT/'SECTION-NEGATIVE-CONTROLS.json').write_text(json.dumps(controls,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'source_models':out['source_models'],'whole_policy_checks':len(out['receipts']),
                      'new_IVT_and_uniqueness_checks':sum('section' in r['kind'] for r in out['receipts']),
                      'action':'unique positive root w^2=first-response[0], then weights(w,1-w)',
                      'negative_controls':len(controls),'generic_synthesis_claimed':False},indent=2))

if __name__=='__main__':main()
