#!/usr/bin/env python3
"""Bounded real-backend integration tests; no mocked source admission.

Each positive/scoped negative source result runs the inherited producer and
semantic checker with all rows sharing one assignment. Use new output each run.
"""
import argparse
import copy
import hashlib
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
    parser.add_argument('--parity-binary')
    parser.add_argument('--parity-sources')
    parser.add_argument('--native-generation',action='store_true')
    a=parser.parse_args()
    a.output.mkdir(parents=True,exist_ok=False)
    owned=['solve.py','certificates.py','external_encoding.py','emit_lean.py','test_solver.py','native_bridge.py']
    def sources():
        return {name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in owned}
    before=sources()
    (a.output/'SOURCE-PINS-BEFORE.json').write_text(json.dumps(before,indent=2)+'\n')
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
        if a.native_generation and task=='generate_singleton':
            cmd+=['--native-generation']
        if a.parity_binary:
            cmd+=['--parity-binary',a.parity_binary,'--parity-sources',a.parity_sources]
        completed=subprocess.run(cmd,capture_output=True,text=True,timeout=100)
        result=json.loads((out/'RESULT.json').read_text())
        passed=completed.returncode==code and result['status']==expected
        if task=='source_search' and expected.startswith('CERTIFIED'):
            inner=result.get('source_result',{})
            passed=passed and inner.get('solver_called') and inner.get('checker_called')
            passed=passed and inner['semantic_check'].get('status') is not None
        if task in ['check_certificate','generate_singleton','common_menu']:
            passed=passed and result.get('source_feasibility_certified') is False
        if a.native_generation and task=='generate_singleton':
            passed=passed and result.get('native_generation',{}).get('agree') is True
        if task=='native_rc1':
            passed=passed and result.get('source_feasibility_certified') is False
            if expected.startswith(('CERTIFIED','CHECKED')):
                passed=passed and result['native_result'].get('certificate_checked') is True
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
              pairs=[dict(i=i,j=j,certificate=generate_singleton(
                  ['1','1','1'] if i==j else ['1','1/2','1/8']
                  if {i,j} in [{'A','B'},{'C','D'}] else ['1','1/4','1/64'])['certificate'])
                  for i in ['A','B','C','D'] for j in ['A','B','C','D']])
    result=run('correlated-menu','common_menu',menu,'UNKNOWN',2)
    r=result['certificate_result']
    assert r['supported_configurations']==['both-left','both-right']
    assert r['conditional_hybrid_budget']==46 and r['budget_applied_to_search'] is False
    queries=json.loads((a.output/'correlated-menu/EXTERNAL-QUERIES.json').read_text())['queries']
    assert len(queries)==48 and all(q['configuration_table']==menu['configurations'] for q in queries)
    assert all(len(q['allocation'])==4+q['level']+1 for q in queries)
    assert queries[2]['comb_coefficient']=='1/18' and queries[2]['required_event_probability']=='1/18'
    assert len(result['Lean_certificate_sources'])==3
    invalid=copy.deepcopy(menu)
    invalid['configurations'][0]['weight']='0'
    run('non-normalized-menu','common_menu',invalid,'REFUSED_REQUEST',1)
    invalid=copy.deepcopy(menu)
    invalid['parameter_constraints']=[{'unmarked_tie':['unprotected-edge','H:1']}]
    run('unencoded-tie','common_menu',invalid,'REFUSED_REQUEST',1)
    if a.parity_binary:
        native_cases=[('native-affine-witness','CERTIFIED_AFFINE_WITNESS',0),
                      ('native-affine-exclusion','CERTIFIED_AFFINE_EXCLUSION',0),
                      ('native-affine-unknown','UNKNOWN',2),
                      ('native-forward-fork','CHECKED_SYMBOLIC_FORWARD_TABLE',0),
                      ('native-forward-common-parallel','CHECKED_SYMBOLIC_FORWARD_TABLE',0),
                      ('native-forward-independent-parallel','CHECKED_SYMBOLIC_FORWARD_TABLE',0)]
        for name,status,code in native_cases:
            sample=json.loads((HERE/'examples'/(name+'.json')).read_text())
            run(name,'native_rc1',sample['input'],status,code)
    assert sources()==before, 'owned source changed during execution'
    result=dict(status='PASS',cases=cases,actual_backend_used=True,source_sha256=before,
                no_Lean_or_universal_native_correctness_claim=True)
    (a.output/'TEST-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='PASS',cases=len(cases))))


if __name__=='__main__':
    main()
