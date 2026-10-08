"""Frozen Git and saved boundary provenance checks; no supplied code executes."""
from pathlib import Path
from fractions import Fraction as F
import subprocess, hashlib, json

C = 'e85ff237dd0d6b3d1e0a939dd923757ba2282d28'
P = 'research/2026-10-08-cloud-gmp-provenance-sol-0035z/'
OLD = 'd90bca775931e3db6f65193b54a4be603427d2a4'
O = Path('research/2026-10-07-cloud-independent-auditor-1616z')
sha = lambda b: hashlib.sha256(b).hexdigest()
ident = lambda b: {'sha256':sha(b), 'bytes':len(b)}
def raw(path, commit=C): return subprocess.check_output(['git','show',commit+':'+path])
def read(path): return raw(P+path)
manifest_b = read('result-manifest.json')
m = json.loads(manifest_b)
artifacts=[]
for r in m['artifacts']:
    b=read(r['path']);assert ident(b)=={k:r[k] for k in ['sha256','bytes']}
    artifacts.append(dict(r,immutable_identity=True))
assert len(artifacts)==79
freeze_b=read('source-freeze.json');freeze=json.loads(freeze_b)
plan_b=read('gate-plan.json');plan=json.loads(plan_b)
wrapper=read('run_provenance_gate.py');published=m['preexecution_published_commit']
assert ident(wrapper)==plan['wrapper'] and sha(wrapper)=='829ef8a9cd774ef7332196a34b3185e05fcb5d7ed8df4cf70495032050136464'
assert ident(freeze_b)==plan['source_freeze']
frozen={};original={};original_checked=[]
for r in freeze['artifacts']+freeze['original_receipts_to_remain_unchanged']:
    b=raw(r['original_path'],r['original_commit'])
    assert ident(b)=={k:r[k] for k in ['sha256','bytes']}
    assert raw(r['original_path'])==b
    original[r['original_path']]=ident(b)
    if 'frozen_path' in r:
        assert read(r['frozen_path'])==b
        frozen[r['frozen_path'].removeprefix('freeze/')]=ident(b)
    original_checked.append(dict(r,original_and_current_byte_identity=True))
assert len(frozen)==7 and len(original)==11
for q in ['run_provenance_gate.py','gate-plan.json','source-freeze.json']+['freeze/'+q for q in frozen]:
    assert raw(P+q,published)==read(q)
r_b=read('results/provenance.json');r=json.loads(r_b)
assert sha(r_b)=='717939a4168b14e8b69dba5e70db30d59df4936944137b8e6f281a0b68aae8b7'
assert r['status']=='PASS' and r['published_freeze_commit']==published
assert r['wrapper']==r['wrapper_after']==ident(wrapper)
assert r['source_freeze']==ident(freeze_b) and r['gate_plan']==ident(plan_b)
assert r['published_source_matches'] and r['source_before_after_equal']
for key in ['frozen_source_before','stage_source_before','source_immediately_before_build','stage_source_after_build','frozen_source_after_build','stage_source_after','frozen_source_after']:
    assert r[key]==frozen
assert r['historical_source_receipts_before']==r['historical_source_receipts_after']==original
for cmd in r['commands']:
    for stream in ['stdout','stderr']:
        row=cmd[stream];assert ident(read('results/'+row['path']))=={k:row[k] for k in ['sha256','bytes']}
    assert cmd['returncode']==0
    stem=cmd['stdout']['path'].removesuffix('.stdout')
    assert json.loads(read('results/'+stem+'.json'))==cmd
assert len(r['commands'])==18
build=[c for c in r['commands'] if '-std=c++17' in c['argv']]
harness=[c for c in r['commands'] if '--harness-child' in c['argv']]
assert len(build)==len(harness)==1
assert read('results/strict-build.stderr')==b''
boundary_b=read('results/native-probe-boundary.json');boundary=json.loads(boundary_b)
execution_b=read('results/harness-buffer-execution.json');execution=json.loads(execution_b)
binary={'sha256':'82880e13a23e0de9ebee4efb9fa3c92daf8ab1c9f4e30fd9f0c9b5d6795b051e','bytes':61944}
assert r['binary_after_build']==r['binary_after_harness']==boundary['binary_before']==boundary['binary_after']==binary
assert boundary['call_count']==execution['native_call_count']==1
assert boundary['returncode']==execution['returncode']==0
assert boundary['source_before']==boundary['source_after']==frozen
assert boundary['harness_buffer']==execution['harness_buffer']==harness[0]['stdin']==frozen['tests/differential.py']
inputs=read('results/batch/differential-inputs.txt');outputs=read('results/batch/probe-output.jsonl')
assert boundary['stdin']==ident(inputs)
for stream in ['stdout','stderr']:
    row=boundary[stream];assert ident(read('results/'+row['path']))=={k:row[k] for k in ['sha256','bytes']}
assert read('results/native-probe.stdout')==outputs and read('results/native-probe.stderr')==b''
assert inputs==raw('research/2026-10-07-cloud-gmp-interval-sol-2354z/results/differential-inputs.txt',OLD)
assert outputs==raw('research/2026-10-07-cloud-gmp-interval-sol-2354z/results/probe-output.jsonl',OLD)
report=json.loads(read('results/batch/differential.json'))
assert r['differential']==report
assert (report['case_count'],report['primitive_comparison_cases'],report['separate_parser_contract_cases'],report['exact_property_assertions'],report['failure_count'])==(2414,2408,6,5204,0)
assert report['status']=='PASS' and report['failures']==[]
assert report['input_sha256']==sha(inputs) and report['cpp_output_sha256']==sha(outputs)
assert len(inputs.splitlines())==len(outputs.splitlines())==2414
targets=[F(1,64),F(1),F(37,8),F(55,2)];found=set()
for line in inputs.decode().splitlines():
    t=line.split()
    if len(t)==3 and t[0]=='exp' and t[2]=='i:64' and t[1][:2] in ('i:','q:'):
        x=F(t[1][2:])
        if x in targets:found.add(x)
truth=r['positive_taylor_truth_gate']
assert found=={F(1)} and truth['status']=='PENDING' and truth['oracle_executed'] is False and truth['native_calls_added']==0
assert truth['found']==['1'] and truth['missing']==['1/64','37/8','55/2']
subprocess.run(['git','merge-base','--is-ancestor',published,C],check=True)
subprocess.run(['git','merge-base','--is-ancestor',C,'origin/main'],check=True)
out={'status':'SOURCE/CODE ACCEPT of ordinary-host finite provenance and saved correspondence',
     'author_commit':C,'preexecution_freeze':published,'wrapper_sha256':sha(wrapper),
     'result_manifest_sha256':sha(manifest_b),'artifact_pins':artifacts,
     'original_source_receipt_pins':original_checked,'provenance_sha256':sha(r_b),
     'boundary_sha256':sha(boundary_b),'buffer_execution_sha256':sha(execution_b),
     'strict_builds':1,'native_probe_batches':1,'source_before_after_equal':True,
     'binary_build_before_after_harness_boundary_equal':binary,
     'new_input_and_output_bytes_identical_to_original_accepted_batch':True,
     'actual_author_primitive_cases':2408,'actual_author_parser_cases':6,'actual_author_property_assertions':5204,
     'positive_taylor_truth_gate':truth,
     'reviewer_wrapper_harness_probe_build_or_oracle_execution':False,
     'limits':['Finite author before/after snapshots on ordinary host; no atomic/hostile-host attestation or independent source-to-binary proof.',
               'Original saved arithmetic was reviewed separately; this additive gate changes provenance only and does not add a universal equivalence, independent exponential truth-oracle PASS, full evaluator/inverse/confidence or benchmark claim.']}
(O/'gmp-provenance-wrapper-source-receipt-authentication.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['artifact_pins','original_source_receipt_pins']},indent=2))
