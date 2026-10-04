#!/usr/bin/env python3
"""Independent exact Fraction checker for the complete two-step real policy.

No SymPy, Z3 or Wolfram verdict is used. Complete actual source-image admission
and surjection are a separately accepted, hash-bound provider.
"""
import argparse
import ast
import copy
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path

NAMES=('sourceSurvival0','sourceSurvival1'); ZERO=(0,0)
def c(x):
    x=F(x);return {ZERO:x} if x else {}
def add(a,b):
    out=dict(a)
    for k,v in b.items():out[k]=out.get(k,F(0))+v
    return {k:v for k,v in out.items() if v}
def scale(a,x):return {k:v*x for k,v in a.items() if v*x}
def mul(a,b):
    out={}
    for k,v in a.items():
        for l,w in b.items():
            m=tuple(x+y for x,y in zip(k,l));out[m]=out.get(m,F(0))+v*w
    return {k:v for k,v in out.items() if v}
def var(i):return {tuple(int(i==j) for j in range(2)):F(1)}
def parse(text):
    def go(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return c(n.value)
        if isinstance(n,ast.Name) and n.id in NAMES:return var(NAMES.index(n.id))
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return scale(go(n.operand),-1)
        if isinstance(n,ast.BinOp):
            a,b=go(n.left),go(n.right)
            if isinstance(n.op,ast.Add):return add(a,b)
            if isinstance(n.op,ast.Sub):return add(a,scale(b,-1))
            if isinstance(n.op,ast.Mult):return mul(a,b)
            if isinstance(n.op,ast.Div) and set(b)=={ZERO}:return scale(a,1/b[ZERO])
            if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant) and type(n.right.value) is int and n.right.value>=0:
                out=c(1)
                for _ in range(n.right.value):out=mul(out,a)
                return out
        raise ValueError('Only rational polynomial arithmetic in the two SAME source parameters is admitted.')
    return go(ast.parse(text,mode='eval').body)

def check(cert,provider_bytes):
    if hashlib.sha256(provider_bytes).hexdigest()!='2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8':raise ValueError('Actual source-image provider changed.')
    provider=json.loads(provider_bytes)
    if provider['source_count']!=546 or provider['source_image_model_count']!=9:raise ValueError('Wrong inherited source coverage.')
    if cert['schema']!='actual-joint-source-genuine-two-step-adaptive-policy-bindings-v1' or cert['source_provider_manifest_sha256']!='3c11ea185f573e6bf47d62a2dde96bd6215aa8eac4073b361f3571557793cbf1':raise ValueError('Wrong policy/provider binding.')
    if cert['path_budget']!=[2,2,1] or cert['optimality_claimed'] is not False or cert['generic_G7_completion_claimed'] is not False:raise ValueError('Policy cost or scope changed.')
    seen=set();s,t=var(0),var(1);one=c(1)
    for r in cert['records']:
        a,b=tuple(r['original_forcing_targets'])
        if (a,b) in seen or (a,b) not in set(itertools.product(range(3),repeat=2)):raise ValueError('Duplicate or invalid source image.')
        seen.add((a,b))
        if r['actual_target_set']!=sorted(set((a,b))) or r['source_parameters']!=list(NAMES):raise ValueError('Target or shared source parameters changed.')
        first=[add(one,scale(s,F(-2,3))) if i==a else scale(s,F(1,3)) for i in range(3)]
        second=[add(one,scale(t,F(-2,3))) if i==b else scale(t,F(1,3)) for i in range(3)]
        w=first[0];v=add(one,scale(w,-1))
        if [parse(x) for x in r['first_observation']]!=first or [parse(x) for x in r['second_action_weights']]!=[w,v]:raise ValueError('Response-dependent action/source row changed.')
        # Real-domain positivity is obtained from these exact simple factors:
        # a=0: w=1-2s/3>1/3, v=2s/3>0; a!=0: w=s/3>0,
        # v=1-s/3>2/3. Both are <1 on 0<s<1.
        expected_w=add(one,scale(s,F(-2,3))) if a==0 else scale(s,F(1,3))
        if w!=expected_w:raise ValueError('Action has no declared strict real-domain proof.')
        out=[add(mul(w,first[i]),mul(v,second[i])) for i in range(3)]
        if [parse(x) for x in r['second_observation']]!=out or add(add(out[0],out[1]),out[2])!=one:raise ValueError('Whole accumulated source response/normalization changed.')
        baseline=scale(add(mul(w,s),mul(v,t)),F(1,3))
        if len(r['identities'])!=3:raise ValueError('Incomplete target guards.')
        for i,identity in enumerate(r['identities']):
            excess={}
            if i==a:excess=add(excess,mul(w,add(one,scale(s,-1))))
            if i==b:excess=add(excess,mul(v,add(one,scale(t,-1))))
            # For every target coordinate this is a NONEMPTY sum of strict
            # positive factors; every non-target excess is exactly zero.
            if identity['coordinate']!=i or type(identity['target_member']) is not bool or identity['target_member']!=(i in (a,b)):raise ValueError('Leaf membership changed.')
            if parse(identity['baseline'])!=baseline or parse(identity['positive_excess'])!=excess or add(baseline,excess)!=out[i]:raise ValueError('Exact leaf positive-factor identity failed.')
        if not set(range(3))-set((a,b)):raise ValueError('A baseline coordinate must exist.')
    if seen!=set(itertools.product(range(3),repeat=2)):raise ValueError('Incomplete whole-policy reachable source coverage.')
    return {'status':'PASS_COMPLETE_REAL_TWO_STEP_POLICY_EXACT_IDENTITIES','source_images':9,
            'shared_source_parameters':True,'all_reachable_response_coverage':'every point of each inherited joint open source square',
            'path_cost':[2,2,1],'action_is_response_dependent':True,
            'identity_checker_uses_QE':False,'source_coverage_and_surjection':'separately accepted actual-source provider',
            'generic_adaptive_policy_synthesis_claimed':False,'optimality_claimed':False}

def main():
    p=argparse.ArgumentParser();p.add_argument('--tamper-controls',action='store_true');a=p.parse_args();root=Path(__file__).resolve().parent
    cert=json.loads((root/'ADAPTIVE-POLICY-CERTIFICATE.json').read_bytes());raw=(root/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes();result=check(cert,raw)
    if a.tamper_controls:
        altered=[]
        z=copy.deepcopy(cert);z['records'].pop();altered.append(z)
        z=copy.deepcopy(cert);z['records'][0]['second_action_weights'][0]='1/2';altered.append(z)
        z=copy.deepcopy(cert);z['records'][0]['second_observation'][0]='1';altered.append(z)
        z=copy.deepcopy(cert);z['records'][0]['actual_target_set']=[1];altered.append(z)
        z=copy.deepcopy(cert);z['path_budget']=[1,2,1];altered.append(z)
        for z in altered:
            try:check(z,raw)
            except (ValueError,KeyError):pass
            else:raise ValueError('Tampered whole-policy certificate accepted.')
        result['tamper_controls_rejected']=len(altered)
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
