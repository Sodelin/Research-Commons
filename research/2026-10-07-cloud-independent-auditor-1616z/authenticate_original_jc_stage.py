"""Read immutable bytes and saved receipts only; never execute the JC runtime."""
from pathlib import Path
from fractions import Fraction
import hashlib, json, subprocess

COMMIT='e91b654db10e863791fa521f0f6b1116b44b5102'
FREEZE='eb18d27f50b5a24dcb26723c484f8708f6e87a22'
BASE='research/2026-10-07-cloud-practical-jc-stage-2351z/'
OWN=Path('research/2026-10-07-cloud-independent-auditor-1616z')
SHA=lambda b:hashlib.sha256(b).hexdigest()
def git(c,p): return subprocess.check_output(['git','show',c+':'+p])
def read(p): return git(COMMIT,BASE+p)
def load(p): return json.loads(read(p))
def canonical(v):return (json.dumps(v,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode()
manifest=load('PUBLIC-FILES.json'); public=[]
for row in manifest['files']:
 b=read(row['path']); assert len(b)==row['bytes'] and SHA(b)==row['sha256']
 public.append({**row,'exact_immutable_Git_file':True})
assert len(public)==22
result=load('attempt1/RESULT.json'); staging=load('attempt1/STAGING.json')
scriptrows=[]
for n,s in result['new_script_sha256'].items():
 b=read(n); assert SHA(b)==s and b==git(FREEZE,BASE+n)
 local=subprocess.check_output(['git','-C','/workspace/cloud-practical','show',result['source_freeze']+':'+BASE+n]); assert b==local
 scriptrows.append({'path':n,'sha256':s,'public_freeze':FREEZE,'recorded_local_freeze':result['source_freeze'],'all_bytes_equal':True})
depraw=git(COMMIT,staging['dependency_manifest']); assert SHA(depraw)==staging['dependency_manifest_sha256']
deps=json.loads(depraw); assert len(deps['files'])==32
checks=[]
for row in deps['files']:
 current=git(COMMIT,row['public_path']); archived=git(row['commit'],row['public_path'])
 blob=subprocess.check_output(['git','rev-parse',row['commit']+':'+row['public_path']],text=True).strip()
 assert current==archived and len(current)==row['bytes'] and SHA(current)==row['sha256'] and blob==row['git_blob']
 recorded={k:row[k] for k in ('public_path','commit','git_blob','sha256','bytes','destination')}
 assert recorded in staging['authenticated_public_sources']
 checks.append({**recorded,'immutable_public_and_archived_bytes_equal':True})
assert len(staging['authenticated_public_sources'])==32
runtime=Path(staging['runtime_root']); runtimechecks=[]
for row in staging['selected_unchanged_runtime_files']:
 p=runtime/row['runtime_relative']; b=p.read_bytes(); assert not p.is_symlink() and SHA(b)==row['sha256'] and len(b)==row['bytes'] and p.stat().st_mode&0o777==0o444
 assert b==git(COMMIT,row['public_path'])
 runtimechecks.append({**row,'reviewer_readback_matches_immutable_original_source':True,'mode':'0444'})
assert len(runtimechecks)==9 and not list(runtime.rglob('*.pyc'))
requestb=read('attempt1/REQUEST.json'); request=json.loads(requestb)
assert SHA(requestb)==staging['request_sha256'] and requestb==(runtime/'REQUEST.json').read_bytes()
oldpath='research/2026-10-05-dot-msci-original-domain-profile-localization-1621z/declared-requests/distinct.json'
oldb=git('52f22ffa9d3ca9b1fc67aa252b3fd3c5ce5c4490',oldpath); assert SHA(oldb)==staging['original_arithmetic_request_sha256']
original=json.loads(oldb)
assert {k:v for k,v in request.items() if k not in ('budget','provenance')}=={k:v for k,v in original.items() if k not in ('budget','provenance')}
assert request['budget']=={'scalar_steps':4,'max_stages':1,'max_splits':0,'max_states':1,'max_depth':0,'wall_ms':3000,'recovery_wall_ms':3000,'recovery_max_stages':1}
assert all(v=='1/20' for v in request['normalized_width_targets'].values()) and len(request['normalized_width_targets'])==9
pinb=read('attempt1/CHECKER-PINS.json'); pins=json.loads(pinb); assert SHA(pinb)==staging['checker_pins_sha256'] and pinb==(runtime/'CHECKER-PINS.json').read_bytes()
for n,s in pins.items(): assert SHA((runtime/staging['engine_directory']/n).read_bytes())==s
assert len(pins)==7
executions=[]
for execution in result['executions']:
 n=execution['name']; saved=load('attempt1/'+n+'-EXECUTION.json'); assert execution==saved
 out=read('attempt1/'+n+'.stdout'); err=read('attempt1/'+n+'.stderr')
 assert SHA(out)==execution['stdout_sha256'] and SHA(err)==execution['stderr_sha256'] and not err
 assert execution['exit']==0 and execution['external_failure'] is None and execution['cpu_seconds_limit']==10 and execution['wall_seconds_limit']==20 and execution['address_space_bytes_limit']==256*1024**2
 assert '-B' in execution['command']
 executions.append({**execution,'saved_stdout_stderr_and_execution_record_match':True})
assert len(executions)==3
assert json.loads(read('attempt1/producer.stdout'))==result['producer'] and json.loads(read('attempt1/checker.stdout'))==result['checker']
frames=[]; previous=None; total=0
for i,row in enumerate(result['complete_new_journal']):
 b=read('attempt1/'+row['path']); assert SHA(b)==row['sha256'] and len(b)==row['bytes']; total+=len(b)
 f=json.loads(b); assert f['sequence']==i and f['parent']==previous and f['request_sha256']==SHA(requestb)
 assert f['sources']=={n:s for n,s in pins.items() if n!='global_check.py'}
 previous={'name':Path(row['path']).name,'sha256':row['sha256']}
 frames.append(f)
assert len(frames)==3 and total==11933 and [f['transition']['kind'] for f in frames]==['genesis','started','applied']
assert frames[1]['transition']['operator']==frames[2]['transition']['operator']=='root'
assert frames[1]['frontier'][0]['status']=='inflight' and frames[2]['frontier'][0]['status']=='pending'
assert frames[2]['frontier'][0]['stage_index']==1 and frames[2]['frontier']==result['checker']['augmented_states']
assert frames[1]['transition']['pre_state_sha256']==SHA(canonical(frames[0]['frontier'][0]['state']))==frames[2]['transition']['pre_state_sha256']
checker=result['checker']; details=checker['details']
assert details['complete_numeric_replay'] and details['journal_frames']==3 and details['authenticated_journal_bytes']==total and details['stages_recomputed']==details['stages_started']==1 and details['splits']==details['exclusions']==0 and not details['resource_limited'] and not details['inflight_pre_state_retained']
assert details['final_commit_sha256']==result['complete_new_journal'][-1]['sha256']
assert checker['status']=='UNKNOWN_OUTER_COVER' and result['producer']['stop_reason']=='stage_budget'
widths={}
cover=checker['physical_cover']; assert len(cover)==1 and cover[0]['box']==frames[2]['frontier'][0]['state']['physical']
for key,ends in cover[0]['box'].items():
 width=Fraction(ends[1])-Fraction(ends[0]); initial=Fraction(request['box'][key][1])-Fraction(request['box'][key][0]); ratio=width/initial
 w=checker['widths'][key]; assert width==Fraction(w['width']) and initial==Fraction(w['original']) and ratio==Fraction(w['normalized_ratio'])
 assert w==result['producer']['widths'][key] and w['met']==(ratio<=Fraction('1/20'))
 assert ratio== (Fraction(1,256) if key=='rR' else Fraction(1))
 widths[key]={'width':str(width),'normalized_ratio':str(ratio),'met':w['met']}
assert not checker['whole_union_width_target_met'] and not checker['statistical_coverage_verified'] and not checker['source_feasibility_certified'] and not checker['parameter_accuracy_released']
subprocess.run(['git','merge-base','--is-ancestor',COMMIT,'origin/main'],check=True)
out={'status':'CODE/SOURCE assembly ACCEPT; saved author execution correspondence PASS; scientific UNKNOWN','author_commit':COMMIT,'public_payloads':public,'scripts':scriptrows,'dependency_manifest_sha256':SHA(depraw),'all32_public_archived_dependency_pins':checks,'selected_runtime_readback':runtimechecks,'runtime_bytecode_currently_absent':True,'only_request_budget_and_provenance_changed':True,'request_sha256':SHA(requestb),'checker_pin_sha256':SHA(pinb),'executions':executions,'journal_frames':3,'journal_bytes':total,'exact_parent_chain_and_request_source_hashes':True,'independent_static_widths':widths,'complete_checker_replay_is_author_execution_not_reviewer_replay':True,'reviewer_provider_solver_checker_or_staging_execution':False,'inherited_mathematical_contractor_theorems_not_reaudited':True,'source_loader_authentication_scope':'fresh controlled unchanged runtime; no hostile-loader theorem','source_feasibility_statistical_admission_all_nine_widths_open':True}
(OWN/'original-jc-staging-source-receipt-authentication.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'author_commit':COMMIT,'public_payloads':len(public),'dependency_pins':len(checks),'selected_runtime_files':len(runtimechecks),'journal_bytes':total,'widths':widths},indent=2))
