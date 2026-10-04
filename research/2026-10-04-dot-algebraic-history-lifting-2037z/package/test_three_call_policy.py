#!/usr/bin/env python3
"""A supplied three-call source policy consuming an algebraic observation."""
import copy
import json
from pathlib import Path
from provider_models import models
from verify_algebraic_policy import verify

ROOT=Path(__file__).resolve().parent
def candidate():
    p=json.loads((ROOT/'ALGEBRAIC-POLICY.json').read_text())
    second=p['next'];decision=second['next']
    # Preserve the full original labelled target decoder; change only which
    # observed full response it reads. No hidden parameter enters the action.
    decision=json.loads(json.dumps(decision).replace('h1_','h2_'))
    second['next']={'kind':'call','support':[0,1],
                    'sections':[{'name':'action_root_lifted','coefficients':['-h1_0','0','1'],'lower':'0','upper':'1'}],
                    'weights':['action_root_lifted','1-action_root_lifted'],'next':decision}
    return p
def run():
    p=candidate();args=(models(),p,[[0],[1],[0,1]],[['H0'],['H0']],[3,2,1])
    result=verify(*args,milliseconds=10000)
    (ROOT/'THREE-CALL-POLICY.json').write_text(json.dumps(p,indent=2)+'\n')
    (ROOT/'THREE-CALL-POLICY-RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
    assert result['status']=='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND',{'status':result['status'],'reason':result.get('reason'),'last':result['receipts'][-1]}
    controls=[]
    for name,change in [('future_observation',lambda q:q['next']['next']['sections'][0].update(coefficients=['-h2_0','0','1'])),
                         ('hidden_source',lambda q:q['next']['next']['sections'][0].update(coefficients=['-s','0','1']))]:
        bad=copy.deepcopy(p);change(bad);out=verify(models(),bad,args[2],args[3],args[4])
        assert out['status']!='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND'
        controls.append({'name':name,'status':out['status'],'reason':out.get('reason')})
    out=verify(models(),p,args[2],args[3],[2,2,1]);assert out['status']=='INVALID_OR_REFUTED_POLICY'
    controls.append({'name':'third_call_exceeds_budget','status':out['status'],'reason':out.get('reason')})
    (ROOT/'THREE-CALL-NEGATIVE-CONTROLS.json').write_text(json.dumps(controls,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'models':result['source_models'],'obligations':len(result['receipts']),'path_budget':[3,2,1],'negative_controls':len(controls),'generic_synthesis_claimed':False}))
if __name__=='__main__':run()
