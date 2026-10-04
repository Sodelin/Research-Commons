#!/usr/bin/env python3
"""Reproduce the inherited two-step obligation and actual-source integration.

The complete nine-image forcing provider is an already accepted source family.
Abstract controls isolate quantifier order/representation bugs; they add no
new biological source case or generic CAD completeness claim.
"""
import itertools
import json
from pathlib import Path
import time
import sympy as sp
import z3
from recursive_engine import WinningFormula, backend_decide, at_most_budget_decide, quantified
from selector_certificate import concrete_selector
from recursive_g7 import run, probability_vector

ROOT=Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def forcing_models():
    s,t=sp.symbols('originalSurvival0 originalSurvival1')
    def row(target,x):
        return [1-2*x/3 if i==target else x/3 for i in range(3)]
    return [{'variables':[s,t],'laws':[row(a,s),row(b,t)],'target':tuple(sorted({a,b}))}
            for a,b in itertools.product(range(3),repeat=2)]


def main():
    started=time.monotonic();models=forcing_models();statuses=[];raw=[]
    for depth, expected in [(0,False),(1,False),(2,True)]:
        engine=WinningFormula(models,[[0],[1]],[{'H0'},{'H0'}],2,1)
        result=backend_decide(engine.win([],depth),3000)
        wanted='CLOSED_RECURSIVE_BUDGET_'+('TRUE' if expected else 'FALSE')+'_SAME_BACKEND'
        require(result['status']==wanted,'Wrong two-step recursive budget')
        statuses.append({'remaining_calls':depth,'status':result['status']});raw.append(result)
    (ROOT/'FINAL-SINGLETON-RECURSION-RECEIPTS.json').write_text(json.dumps(raw,indent=2)+'\n')
    engine=WinningFormula(models,[[0],[1]],[{'H0'},{'H0'}],2,1)
    selector=concrete_selector(engine,[[z3.RealVal(1),z3.RealVal(0)],[z3.RealVal(0),z3.RealVal(1)]],2,3000)
    require(selector['status']=='CONCRETE_SELECTOR_AND_ACTUAL_SOURCE_DECODER_CERTIFIED_SAME_BACKEND','Two-step selector failed')
    (ROOT/'FINAL-TWO-STEP-SELECTOR.json').write_text(json.dumps(selector,indent=2)+'\n')
    engine=WinningFormula(models,[[0,1]],[{'H0'},{'H0'}],2,1)
    monotone=at_most_budget_decide(engine,[],2,milliseconds=3000)
    require(monotone['status']=='AT_MOST_BUDGET_TRUE_BY_COMPLETED_LOWER_BUDGET_CHECK'
            and monotone['winning_remaining_programmes']==1,'Accepted terminal source reduction did not integrate')
    (ROOT/'FINAL-MONOTONE-CONTINUOUS-RECEIPT.json').write_text(json.dumps(monotone,indent=2)+'\n')
    # The wrong existential response must not pass as a universal strategy.
    x=sp.Symbol('sharedOriginalParameter')
    abstract=[{'variables':[x],'laws':[[x,1-x]],'target':0},
              {'variables':[x],'laws':[[x/2,1-x/2]],'target':1}]
    engine=WinningFormula(abstract,[[0]],[set()],1,0)
    correct=backend_decide(engine.win([],1),3000)
    response=[z3.FreshReal('exactResponse') for _ in range(2)];weights=[z3.RealVal(1)]
    possible=[]
    for model in abstract:
        symbols={x:z3.FreshReal('originalParameter')}
        _,conditions=engine.consistency(model,symbols,[(weights,response)])
        possible.append(quantified(list(symbols.values()),z3.And(*conditions)))
    wrong=backend_decide(z3.Exists(response,z3.And(z3.Or(*possible),engine.homogeneous([(weights,response)]))),3000)
    require(correct['status']=='CLOSED_RECURSIVE_BUDGET_FALSE_SAME_BACKEND'
            and wrong['status']=='CLOSED_RECURSIVE_BUDGET_TRUE_SAME_BACKEND','Quantifier-order control is ineffective')
    # Exact algebraic concrete history admission, not just rational observations.
    a=z3.Real('algebraicObserved');solve=z3.SolverFor('QF_NRA');solve.add(2*a*a==1,a>0)
    require(solve.check()==z3.sat,'Algebraic control failed')
    from solver import encode_value
    value=solve.model()[a]
    probability_vector([encode_value(value),encode_value(1-value if z3.is_algebraic_value(1-value) else z3.simplify(1-value))],2)
    request=json.loads((ROOT/'examples/actual-source-root.json').read_text())
    actual=run(request,ROOT/'runs/final-actual-source-root')
    require(actual['status']=='RECURSIVE_BUDGET_TRUE_CONCRETE_SELECTOR_CERTIFIED_SAME_BACKEND',
            'Actual-source budget/selector/decoder pipeline failed')
    (ROOT/'runs/final-actual-source-root/RECURSIVE-RESULT.json').write_text(json.dumps(actual,indent=2)+'\n')
    receipt={'schema':'recursive-G7-obligation-terminal-test-v1','status':'PASS',
             'accepted_source_image_provider_manifest_sha256':'3c11ea185f573e6bf47d62a2dde96bd6215aa8eac4073b361f3571557793cbf1',
             'source_family_expanded':False,'source_shared_parameters_preserved':True,
             'singleton_support_recursive_budgets':statuses,'two_step_selector':selector['status'],
             'at_most_budget_reuse':monotone['status'],'actual_source_pipeline':actual['status'],
             'abstract_quantifier_order_control':'PASS','exact_algebraic_history_probability_vector':'PASS',
             'generic_adaptive_CAD_completeness_claimed':False,
             'trust':'Completed recursive decisions/selectors use explicit same-backend QE; no Lean certification',
             'elapsed_seconds':time.monotonic()-started,'z3':z3.get_version_string()}
    (ROOT/'TEST-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'actual_source_pipeline':actual['status'],
                      'elapsed_seconds':receipt['elapsed_seconds']},indent=2))


if __name__=='__main__':
    main()
