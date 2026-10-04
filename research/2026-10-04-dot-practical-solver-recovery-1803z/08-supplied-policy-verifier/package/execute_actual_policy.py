#!/usr/bin/env python3
"""Execute a verified finite adaptive policy with coherent observed history.

The response codec is exact rational. The verified policy is quantified over
all real source parameters and actions; unsupported codecs remain UNKNOWN.
"""
import argparse
import ctypes
from fractions import Fraction
import json
from pathlib import Path
import sys
import sympy as sp
import z3
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'terminalkit'))
from verify_actual_policy import run
from terminal_g7 import parse_polynomial
from solver import rational
from terminal_engine import polynomial_to_z3
from verify_policy import expression,guard,PolicyEncodingError

def replay(request,directory):
    directory=Path(directory)
    if not isinstance(request,dict) or request.get('schema')!='execute-actual-source-finite-adaptive-policy-v1':
        raise ValueError('Wrong execution request shape/schema.')
    observations=request.get('observed_responses',[])
    if not isinstance(observations,list):raise ValueError('Observed responses must be a finite list.')
    verification={k:v for k,v in request.items() if k!='observed_responses'}
    verification['schema']='actual-source-finite-adaptive-policy-verification-v1'
    certified=run(verification,directory/'verification')
    if certified['status']!='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND':
        return {'status':'UNKNOWN_UNCERTIFIED_POLICY','verification':certified}
    provider=json.loads((directory/'verification/source-export/ACTUAL-SOURCE-MODELS.json').read_bytes())
    k=len(provider['models'][0]['laws']);q=len(provider['models'][0]['laws'][0]);obs={};history=[];admissions=[]
    def vector(data,n):
        if not isinstance(data,list) or len(data)!=n:raise ValueError('Missing/extra exact history coordinates.')
        out=[Fraction(str(rational(v))) for v in data]
        if sum(out)!=1 or any(v<0 for v in out):raise ValueError('History vector is not an exact probability vector.')
        return out
    for i,row in enumerate(verification.get('history',[])):
        weights=vector(row['row_weights'],k);response=vector(row['response'],q);history.append((weights,response))
        obs.update({f'h{i}_{j}':z3.RealVal(str(v)) for j,v in enumerate(response)})
    ms=verification.get('backend_limits',{}).get('per_query_ms',3000)
    def admit():
        unknown=False;rows=[]
        for i,record in enumerate(provider['models']):
            syms={n:sp.Symbol(n) for n in record['variable_mapping'].values()}
            point={v:z3.FreshReal('oneOriginalHistoryParameter') for v in syms.values()}
            laws=[[polynomial_to_z3(parse_polynomial(p,syms),point) for p in row] for row in record['laws']]
            constraints=[z3.And(v>0,v<1) for v in point.values()]
            for weights,response in history:
                constraints += [sum(z3.RealVal(str(weights[a]))*laws[a][j] for a in range(k))==z3.RealVal(str(response[j])) for j in range(q)]
            solver=z3.SolverFor('QF_NRA');solver.set(timeout=ms);solver.add(*constraints);status=solver.check()
            row={'source_model':i,'status':str(status),'query_smt2':solver.to_smt2()}
            if status==z3.sat:
                row.update(original_source=record['source'],mechanism=record['mechanism'],actual_target=record['actual_target'],
                           original_parameter_assignment={old:str(solver.model().eval(point[syms[new]],model_completion=True)) for old,new in record['variable_mapping'].items()})
                rows.append(row);admissions.append({'history_length':len(history),'status':'JOINT_ACTUAL_HISTORY_ADMITTED_SAME_BACKEND','receipts':rows});return True
            if status==z3.unknown:unknown=True;row['reason']=solver.reason_unknown()
            rows.append(row)
        admissions.append({'history_length':len(history),'status':'UNKNOWN_HISTORY_ADMISSION' if unknown else 'NO_ADMITTED_SOURCE_FOR_COMPLETE_HISTORY_SAME_BACKEND','receipts':rows})
        return False
    if not admit():return {'status':'UNKNOWN_OR_IMPOSSIBLE_ACTUAL_HISTORY','admissions':admissions}
    node=request['policy'];taken=0;steps=[]
    while True:
        if node['kind']=='leaf':
            if taken!=len(observations):raise ValueError('Responses remain after the policy already reached a target leaf.')
            return {'status':'IDENTIFIED_ACTUAL_TARGET_BY_VERIFIED_ADAPTIVE_POLICY_SAME_BACKEND','actual_target':node['target'],
                    'executed_actions':steps,'admissions':admissions,'verification_status':certified['status'],
                    'actual_source_models_sha256':certified['actual_source_models_sha256'],
                    'empirical_admission_claimed':False,'generic_adaptive_synthesis_claimed':False,
                    'runtime_response_codec':'exact rational; unsupported codecs remain UNKNOWN'}
        if node['kind']=='decision':
            chosen=None
            for branch in node['branches']:
                g,defined=guard(branch['guard'],obs)
                if not z3.is_true(z3.simplify(defined)):raise ValueError('Observed guard is undefined.')
                answer=z3.simplify(g)
                if z3.is_true(answer):chosen=branch['next'];break
                if not z3.is_false(answer):raise ValueError('Observed guard could not be exactly evaluated.')
            if chosen is None:raise ValueError('Observed history has no certified reachable branch.')
            node=chosen;continue
        values=[]
        for text in node['weights']:
            v,defined=expression(text,obs);v=z3.simplify(v)
            if not z3.is_true(z3.simplify(defined)) or not z3.is_rational_value(v):raise ValueError('Action has no supported exact rational runtime encoding.')
            values.append(v.as_fraction())
        action={'original_row_weights':[str(v) for v in values],'support_zero_based':node['support']}
        if taken==len(observations):
            return {'status':'NEXT_VERIFIED_SOURCE_ADMITTED_ACTION','action':action,'executed_actions':steps,
                    'admissions':admissions,'verification_status':certified['status'],
                    'actual_source_models_sha256':certified['actual_source_models_sha256'],
                    'empirical_admission_claimed':False,'generic_adaptive_synthesis_claimed':False}
        response=vector(observations[taken],q);h=len(history);history.append((values,response));steps.append(action)
        obs.update({f'h{h}_{j}':z3.RealVal(str(v)) for j,v in enumerate(response)})
        if not admit():return {'status':'UNKNOWN_OR_IMPOSSIBLE_ACTUAL_HISTORY','admissions':admissions,'executed_actions':steps}
        taken+=1;node=node['next']

def main():
    p=argparse.ArgumentParser();p.add_argument('request');p.add_argument('--output',required=True);a=p.parse_args();outdir=Path(a.output);outdir.mkdir(parents=True,exist_ok=True)
    try:out=replay(json.loads(Path(a.request).read_bytes()),outdir)
    except (RecursionError,ctypes.ArgumentError) as e:out={'status':'UNKNOWN_POLICY_ENCODING_RESOURCE_LIMIT','reason':str(e),'empirical_admission_claimed':False}
    except (ValueError,TypeError,KeyError,SyntaxError,z3.Z3Exception) as e:out={'status':'UNKNOWN_INVALID_OR_UNSUPPORTED_POLICY_EXECUTION','reason':str(e),'empirical_admission_claimed':False}
    (outdir/'EXECUTION-RESULT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ('admissions','verification')},indent=2))

if __name__=='__main__':main()
