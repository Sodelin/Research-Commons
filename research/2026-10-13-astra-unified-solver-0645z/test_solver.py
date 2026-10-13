#!/usr/bin/env python3
"""Bounded real-backend integration tests; no mocked source admission.

Each positive/scoped negative source result runs the inherited producer and
semantic checker with all rows sharing one assignment. Use new output each run.
"""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys

from certificates import generate_singleton

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--backend-python',required=True)
    parser.add_argument('--rust-binary')
    a=parser.parse_args()
    a.output.mkdir(parents=True,exist_ok=False)
    cases=[]
    def run(name, task, request, expected, code):
        incoming=dict(schema='unified_research_solver_v1',task=task,input=request)
        source=a.output/(name+'.json')
        source.write_text(json.dumps(incoming,indent=2)+'\n')
        out=a.output/name
        cmd=[sys.executable,'-B',str(HERE/'solve.py'),'--request',str(source),
             '--output',str(out),'--backend-python',a.backend_python]
        if a.rust_binary:
            cmd+=['--rust-binary',a.rust_binary]
        completed=subprocess.run(cmd,capture_output=True,text=True,timeout=100)
        result=json.loads((out/'RESULT.json').read_text())
        passed=completed.returncode==code and result['status']==expected
        if task=='source_search' and expected.startswith('CERTIFIED'):
            inner=result.get('source_result',{})
            passed=passed and inner.get('solver_called') and inner.get('checker_called')
            passed=passed and inner['semantic_check'].get('status') is not None
        if task in ['check_certificate','generate_singleton','common_menu']:
            passed=passed and result.get('source_feasibility_certified') is False
        cases.append(dict(name=name,passed=bool(passed),status=result['status'],
                          exit_code=completed.returncode,output=str(out)))
        (a.output/(name+'.stdout')).write_text(completed.stdout)
        (a.output/(name+'.stderr')).write_text(completed.stderr)
        (a.output/'TEST-RESULT.json').write_text(json.dumps(dict(cases=cases),indent=2)+'\n')
        if not passed:
            raise AssertionError(cases[-1])
        return result
    examples=ROOT/'applications/practical-solver/examples/certified-bounds'
    source_cases=[('finite-witness','CERTIFIED_SOURCE_WITNESS',0),
                  ('bounded-witness','CERTIFIED_SOURCE_WITNESS',0),
                  ('shared-row-exclusion','CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS',0),
                  ('strict-positivity-exclusion','CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS',0),
                  ('bounded-exhaustion','UNKNOWN',2),
                  ('conditional-count-unknown','UNKNOWN',2)]
    for name, status, code in source_cases:
        run(name,'source_search',json.loads((examples/(name+'.json')).read_text()),status,code)
    run('singleton-generator','generate_singleton',['1','1/2','1/8'],'GENERATED_AND_CHECKED',0)
    run('generator-unknown','generate_singleton',['1','1/2','1/4'],'UNKNOWN',2)
    cert=generate_singleton(['1','1/2','1/8'])['certificate']
    run('certificate','check_certificate',cert,'CHECKED_RATIONAL_CERTIFICATE',0)
    broken=copy.deepcopy(cert)
    broken['coefficients'][0]='1/3'
    run('forged-identity','check_certificate',broken,'REFUSED_REQUEST',1)
    menu=dict(schema='supplied_common_menu_v1',taxa=['A','B','C','D'],
              protected_edges=[],protected_hybrids=['H:1','H:2'],parameter_constraints=[],
              configurations=[dict(id='both-left',weight='1/2',mask={'H:1':0,'H:2':0}),
                              dict(id='both-right',weight='1/2',mask={'H:1':1,'H:2':1}),
                              dict(id='zero-mass',weight='0',mask={'H:1':None,'H:2':None})],
              pairs=[dict(i=i,j=j,certificate=cert) for i in ['A','B','C','D'] for j in ['A','B','C','D']])
    result=run('correlated-menu','common_menu',menu,'UNKNOWN',2)
    r=result['certificate_result']
    assert r['supported_configurations']==['both-left','both-right']
    assert r['conditional_hybrid_budget']==46 and r['budget_applied_to_search'] is False
    invalid=copy.deepcopy(menu)
    invalid['configurations'][0]['weight']='0'
    run('non-normalized-menu','common_menu',invalid,'REFUSED_REQUEST',1)
    invalid=copy.deepcopy(menu)
    invalid['parameter_constraints']=[{'unmarked_tie':['unprotected-edge','H:1']}]
    run('unencoded-tie','common_menu',invalid,'REFUSED_REQUEST',1)
    result=dict(status='PASS',cases=cases,actual_backend_used=True,
                no_Lean_or_universal_native_correctness_claim=True)
    (a.output/'TEST-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',cases=len(cases))))


if __name__=='__main__':
    main()
