#!/usr/bin/env python3
"""Actual complete source export -> finite adaptive candidate verification."""
import argparse
import ctypes
import hashlib
import json
from pathlib import Path
import sys
import sympy as sp
import z3
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'terminalkit'))
from terminal_g7 import verify_base, parse_polynomial, require, InvalidInput, Unsupported
from export_design import export, validated
from solver import rational
from verify_policy import verify

def run(request,directory):
    require(isinstance(request,dict) and set(request)<={'schema','design_request','policy','history','budget','backend_limits'},'Unsupported policy-verification fields.')
    require(request.get('schema')=='actual-source-finite-adaptive-policy-verification-v1','Wrong request schema.')
    binding=json.loads((ROOT/'TERMINAL-BASE-BINDING.json').read_bytes())
    for r in binding['files']:
        require(hashlib.sha256((ROOT/r['path']).read_bytes()).hexdigest()==r['sha256'],'Reviewed terminal source binding changed.')
    verify_base()
    design=request['design_request']
    n,ids,modes,samples,readout,target,forces,supports,budgets,limits=validated(design)
    budget=request['budget'];require(budget in budgets,'PATH budget must be explicitly declared in the source design.')
    support_menu=[sorted(i-1 for i in support) for support in supports]
    backend=request.get('backend_limits',{})
    require(isinstance(backend,dict) and set(backend)<={'per_query_ms','max_nodes'},'Unknown backend fields.')
    ms=backend.get('per_query_ms',3000);cap=backend.get('max_nodes',10000)
    require(type(ms) is int and 0<ms<=60000 and type(cap) is int and cap>0,'Positive bounded query time/node limits required.')
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    exported=export(design,directory/'source-export')
    if exported.get('catalogue_exhausted') is not True:
        return {'status':'UNKNOWN_INCOMPLETE_ACTUAL_SOURCE_EXPORT','export':exported,'policy_verified':False}
    provider_path=directory/'source-export/ACTUAL-SOURCE-MODELS.json';provider=json.loads(provider_path.read_bytes());models=[]
    for record in provider['models']:
        variables={name:sp.Symbol(name) for name in record['variable_mapping'].values()}
        models.append({'variables':list(variables.values()),'laws':[[parse_polynomial(p,variables) for p in row] for row in record['laws']],
                       'target':record['actual_target']})
    history=[]
    for row in request.get('history',[]):
        require(isinstance(row,dict) and set(row)=={'row_weights','response'},'Unknown or missing initial-history fields.')
        require(isinstance(row['row_weights'],list) and isinstance(row['response'],list),'Initial history must contain full exact vectors.')
        history.append(([rational(v) for v in row['row_weights']],[rational(v) for v in row['response']]))
    result=verify(models,request['policy'],support_menu,[set(op) for op in design['deterministic_rows']],budget,history,ms,cap)
    result.update(schema='actual-source-adaptive-policy-verification-result-v1',
                  actual_source_models_sha256=hashlib.sha256(provider_path.read_bytes()).hexdigest(),
                  actual_source_count=provider['source_count_examined'],catalogue_exhausted=True,
                  target_kind=target,observations='full exact inherited unranked readout',
                  target_serialization='actual original engine-labelled target; not only an arbitrary target code',
                  complete_original_registry=True,empirical_admission_claimed=False,Lean_certification_claimed=False,
                  unknown_size_termination_or_global_NO_claimed=False,generic_adaptive_policy_synthesis_claimed=False,
                  source_export_trust='inherited admitted source census/compiler and completed exact algebra; no Lean proof of this Python execution',
                  software={'sympy':sp.__version__,'z3':z3.get_version_string()})
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('request');p.add_argument('--output',required=True);a=p.parse_args();directory=Path(a.output);directory.mkdir(parents=True,exist_ok=True)
    try:out=run(json.loads(Path(a.request).read_bytes()),directory)
    except (RecursionError,ctypes.ArgumentError) as e:out={'status':'UNKNOWN_POLICY_ENCODING_RESOURCE_LIMIT','reason':str(e),'policy_verified':False,'empirical_admission_claimed':False}
    except (ValueError,TypeError,KeyError,SyntaxError,z3.Z3Exception) as e:out={'status':'REJECTED_ACTUAL_POLICY_INPUT','reason':str(e),'policy_verified':False,'empirical_admission_claimed':False}
    (directory/'POLICY-RESULT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ('receipts','export')},indent=2))

if __name__=='__main__':main()
