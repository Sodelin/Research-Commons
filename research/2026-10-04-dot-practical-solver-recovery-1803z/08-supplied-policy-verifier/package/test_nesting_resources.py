#!/usr/bin/env python3
"""Excess nesting must remain an explicit resource UNKNOWN, never crash/NO."""
import json
from pathlib import Path
import sympy as sp
from verify_policy import verify

def main():
    x=sp.Symbol('originalX');source=[{'variables':[x],'laws':[[x,1-x]],'target':'A'}]
    tree={'kind':'leaf','target':'A'}
    for _ in range(1100):tree={'kind':'decision','branches':[{'guard':True,'next':tree}]}
    cases=[]
    out=verify(source,tree,[[0]],[[]],[0,0,0],max_nodes=5000)
    assert out['status']=='UNKNOWN_POLICY_VERIFICATION_RESOURCE_LIMIT',out;cases.append({'case':'1100_nested_policy_nodes','result':out})
    g=True
    for _ in range(1100):g={'op':'not','arg':g}
    guarded={'kind':'decision','branches':[{'guard':g,'next':{'kind':'leaf','target':'A'}}]}
    out=verify(source,guarded,[[0]],[[]],[0,0,0],max_nodes=5000)
    assert out['status']=='UNKNOWN_POLICY_VERIFICATION_RESOURCE_LIMIT',out;cases.append({'case':'1100_nested_guards','result':out})
    expression='+'.join(['1']*1100)
    call={'kind':'call','support':[0],'weights':[expression],'next':{'kind':'leaf','target':'A'}}
    out=verify(source,call,[[0]],[[]],[1,1,0],max_nodes=5000)
    assert out['status']=='UNKNOWN_POLICY_VERIFICATION_RESOURCE_LIMIT',out;cases.append({'case':'1100_term_expression_depth','result':out})
    cycle={'kind':'decision','branches':[]};cycle['branches']=[{'guard':True,'next':cycle}]
    out=verify(source,cycle,[[0]],[[]],[0,0,0],max_nodes=5000)
    assert out['status']=='UNKNOWN_POLICY_VERIFICATION_RESOURCE_LIMIT',out;cases.append({'case':'cyclic_direct_API_policy','result':out})
    shallow={'kind':'decision','branches':[{'guard':True,'next':{'kind':'leaf','target':'A'}}]}
    assert verify(source,shallow,[[0]],[[]],[0,0,0])['status']=='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND'
    root=Path(__file__).resolve().parent;(root/'NESTING-RESOURCE-CONTROLS.json').write_text(json.dumps(cases,indent=2)+'\n');print(json.dumps({'status':'PASS_EXPLICIT_NESTING_RESOURCE_UNKNOWN','controls':len(cases)},indent=2))

if __name__=='__main__':main()
