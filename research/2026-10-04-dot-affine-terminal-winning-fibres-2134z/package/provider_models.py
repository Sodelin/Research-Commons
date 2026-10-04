#!/usr/bin/env python3
"""Test the decisive generic fixed-policy verifier on the accepted source image."""
import copy
import hashlib
import itertools
import json
from pathlib import Path
import sympy as sp
from verify_policy import verify

ROOT=Path(__file__).resolve().parent
def models():
    raw=(ROOT/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8'
    provider=json.loads(raw)
    pairs=[tuple(r['forced_rows'][i]['target_coordinate'] for i in (0,1)) for r in provider['surjection_representatives']]
    assert set(pairs)==set(itertools.product(range(3),repeat=2)) and len(pairs)==9
    s,t=sp.symbols('sameOriginalSurvival0 sameOriginalSurvival1')
    def row(a,v):return [1-2*v/3 if i==a else v/3 for i in range(3)]
    return [{'variables':[s,t],'laws':[row(a,s),row(b,t)],'target':tuple(sorted({a,b}))}
            for a,b in pairs]

def policy():
    branches=[]
    for target in [(0,),(1,),(2,),(0,1),(0,2),(1,2)]:
        outside=next(i for i in range(3) if i not in target)
        guards=[{'op':'gt' if i in target else 'eq','left':f'h1_{i}','right':f'h1_{outside}'}
                for i in range(3) if i!=outside]
        branches.append({'guard':{'op':'and','args':guards},'next':{'kind':'leaf','target':list(target)}})
    return {'kind':'call','support':[0],'weights':['1','0'],
            'next':{'kind':'call','support':[0,1],'weights':['h0_0','1-h0_0'],
                    'next':{'kind':'decision','branches':branches}}}

def run():
    sources=models();candidate=policy();args=(sources,candidate,[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1])
    result=verify(*args);assert result['status']=='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND',result
    (ROOT/'POLICY.json').write_text(json.dumps(candidate,indent=2)+'\n')
    (ROOT/'VERIFIED-POLICY-RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
    controls=[]
    def reject(p,budget=[2,2,1],history=(),status='INVALID_OR_REFUTED_POLICY',**kwargs):
        out=verify(sources,p,[[0],[1],[0,1]],[['H0'],['H0']],budget,initial_history=history,**kwargs)
        assert out['status']==status,out;controls.append({'expected':status,'result':out})
    p=copy.deepcopy(candidate);p['next']['weights']=['sameOriginalSurvival0','1-sameOriginalSurvival0'];reject(p)
    p=copy.deepcopy(candidate);p['next']['weights']=['h1_0','1-h1_0'];reject(p)
    p=copy.deepcopy(candidate);p['next']['weights']=['1/(h0_0-h0_0)','0'];reject(p)
    p=copy.deepcopy(candidate);p['next']['weights']=['h0_0','h0_0'];reject(p)
    p=copy.deepcopy(candidate);p['next']['next']['branches'].pop();reject(p)
    p=copy.deepcopy(candidate);p['next']['next']['branches'][0]['next']['target']=[1];reject(p)
    p=copy.deepcopy(candidate);p['weights']=['1'];reject(p)
    reject(candidate,budget=[1,2,1]);reject(candidate,budget=[2,1,1]);reject(candidate,budget=[2,2,0])
    reject(candidate,max_nodes=1,status='UNKNOWN_POLICY_VERIFICATION_RESOURCE_LIMIT')
    impossible=[([sp.Rational(1),sp.Rational(0)],[sp.Rational(1,3)]*3)]
    reject(candidate,history=impossible,status='NO_ADMITTED_SOURCE_FOR_INITIAL_HISTORY_SAME_BACKEND')
    (ROOT/'ADVERSARIAL-CONTROLS.json').write_text(json.dumps(controls,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'source_models':result['source_models'],
                      'exact_source_obligations':len(result['receipts']),'negative_controls':len(controls),
                      'source_family_expanded':False,'generic_synthesis_claimed':False},indent=2))

if __name__=='__main__':run()
