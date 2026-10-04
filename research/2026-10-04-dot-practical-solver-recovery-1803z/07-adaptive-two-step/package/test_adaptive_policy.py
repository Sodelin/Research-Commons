#!/usr/bin/env python3
"""Replay source-admitted adaptive paths and adversarial history controls."""
import copy
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
from execute_adaptive_policy import execute
from verify_adaptive_certificate import check

ROOT=Path(__file__).resolve().parent
def forced(a,s):return [1-2*s/3 if i==a else s/3 for i in range(3)]
def template():return {'observation_kind':'exact_unranked_law','n':4,
                      'registry':{'complete':True,'hybrid_ids':['H0']},
                      'mechanism':'independent','path_budget':[2,2,1],'history':[]}

def run():
    certificate=check(json.loads((ROOT/'ADAPTIVE-POLICY-CERTIFICATE.json').read_bytes()),(ROOT/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes())
    complete=[]
    for mode in ('independent','common'):
        for a in range(3):
            for b in range(3):
                request=template();request['mechanism']=mode
                assert execute(request)['programme']==[{'weight':'1','forced':{'H0':0}}]
                s,t=F(1,2),F(2,3);h=forced(a,s);g=forced(b,t);w=h[0]
                z=[w*h[i]+(1-w)*g[i] for i in range(3)]
                request['history']=[[str(v) for v in h]]
                action=execute(request)
                assert action['status']=='ACTION' and action['programme'][0]['weight']==str(w)
                request['history'].append([str(v) for v in z])
                result=execute(request)
                assert result['status']=='IDENTIFIED_ACTUAL_Q_BY_RESPONSE_DEPENDENT_TWO_STEP_POLICY',result
                assert result['ordered_forcing_targets']==[a,b] and result['path_cost']==[2,2,1]
                complete.append({'request':request,'result':result})
    # Different reachable first responses choose genuinely different actions.
    choices=[]
    for s in (F(1,3),F(2,3)):
        q=template();q['history']=[[str(v) for v in forced(0,s)]];choices.append(execute(q)['programme'])
    assert choices[0]!=choices[1]
    prefix_witnesses=[path for path in complete if path['request']['mechanism']=='independent' and path['result']['ordered_forcing_targets'] in ([0,0],[0,1])]
    assert len(prefix_witnesses)==2
    assert prefix_witnesses[0]['request']['history'][0]==prefix_witnesses[1]['request']['history'][0]
    assert prefix_witnesses[0]['result']['identified_target']!=prefix_witnesses[1]['result']['identified_target']
    controls=[]
    q=template();q['history']=[['1/3','1/3','1/3']];controls.append(q)
    q=template();q['history']=[['2/3','1/6','1/6'],['1/6','2/3','1/6']];controls.append(q)
    q=template();q['history']=[[0.7,0.15,0.15]];controls.append(q)
    q=template();q['empirical_admission']={'status':'ADMITTED'};controls.append(q)
    q=template();q['empirical_admission']=[];controls.append(q)
    q=template();q['observation_kind']='DNA';controls.append(q)
    q=template();q['path_budget']=[1,2,1];controls.append(q)
    q=template();q['history']=[['1/2','1/2']];controls.append(q)
    q=template();q['external_weights']=['1/2','1/2'];controls.append(q)
    q=template();q['mechanism']='per-row-fit';controls.append(q)
    q=template();q['history']=[['2/3','1/6','1/6'],['1/3','1/3','1/3']];controls.append(q)
    rejected=[]
    for q in controls:
        result=execute(q);assert result['status'].startswith('UNKNOWN'),result;rejected.append({'request':q,'result':result})
    result={'status':'PASS_COMPLETE_TWO_STEP_ADAPTIVE_SOURCE_PATH_REPLAY','actual_source_history_recompilations':len(complete),
            'mechanisms':['independent','common'],'all_nine_joint_source_images_checked':True,
            'genuine_response_dependent_actions':choices,'first_step_ambiguity_witnesses':prefix_witnesses,'independent_real_certificate':certificate,
            'negative_controls_rejected':len(rejected),'paths':complete,'negative_controls':rejected,
            'runtime_exact_rational_encoding_only':True,'generic_adaptive_synthesis_claimed':False}
    (ROOT/'runs'/'SOURCE-PATH-REPLAY.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('paths','negative_controls','first_step_ambiguity_witnesses')},indent=2))

if __name__=='__main__':run()
