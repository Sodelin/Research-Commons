"""Compare preserved author artifacts to independently retrieved terminal bytes; no compiler."""
from pathlib import Path
import hashlib, json, re, subprocess, sys
from datetime import datetime

BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[1]
PREFIX='three-followon-pass-37738512508'
AUTHOR=sys.argv[1]
PUBLIC='research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/evidence/g6-run-37738512508-PASS/'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(path):return subprocess.check_output(['git','show',AUTHOR+':'+path],cwd=ROOT)
def extract(raw):
    msgs=[re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '',l.split('\t',2)[-1].lstrip('\ufeff')) for l in raw.decode().splitlines()]
    inputs=next(json.loads(m.split(' ',1)[1]) for m in msgs if m.startswith('G6_INPUTS '))
    receipts,out,pending,lines=[],{},None,[]
    for m in msgs:
        if m.startswith('G6_COMMAND '):
            assert pending is None
            pending=json.loads(m.split(' ',1)[1]);lines=[]
        elif m.startswith('G6_RECEIPT '):
            assert pending is not None
            r=json.loads(m.split(' ',1)[1]);assert pending['argv']==r['argv']
            label=Path(r['argv'][-1]).stem if r['argv'][1:3]==['env','lean'] else 'cache'
            out[label]=('\n'.join(lines)+('\n' if lines else '')).encode()
            receipts.append(r);pending=None
        elif pending is not None:lines.append(m)
    assert pending is None
    return inputs,receipts,out

official=(BASE/(PREFIX+'-actions.log')).read_bytes()
assert official==git(PUBLIC+'original-connector-job.log')
i,r,o=extract(official);ai,ar,ao=extract(git(PUBLIC+'actions.log'))
assert i==ai and r==ar and len(r)==182
assert json.loads(git(PUBLIC+'inputs-recovered.json'))==i
assert json.loads(git(PUBLIC+'receipts-recovered.json'))==r
correspondence=[]
for label,data in o.items():
    if label=='cache':continue
    assert data==ao[label],label
    correspondence.append({'label':label,'stdout_sha256':sha(data),'byte_equal':True})
assert len(correspondence)==181
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',AUTHOR,PUBLIC],cwd=ROOT).decode().splitlines()
artifacts=[]
for path in paths:
    b=git(path)
    artifacts.append({'path':path,'bytes':len(b),'sha256':sha(b),'git_blob':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()})
saved_stdout_checks=[]
for path in paths:
    name=Path(path).name
    if name.endswith('-actual.log'):
        label=name[:-len('-actual.log')]
        assert label in o and git(path)==o[label],path
        saved_stdout_checks.append({'path':path,'bytes':len(o[label]),'sha256':sha(o[label]),'byte_equal':True})
transport=json.loads(git(PUBLIC+'transport-normalization.json'))
assert transport['original_sha256']==sha(official)
assert transport['corrected_normalized_sha256']==sha(git(PUBLIC+'actions.log'))
assert transport['rejected_normalized_sha256']!=transport['corrected_normalized_sha256']
assert o['HybridSizeCore']==b'' and git(PUBLIC+'HybridSizeCore-actual.log')==b''
assert sha(git(PUBLIC+'recover-g6-api-owned-run-v2-empty-stdout.py'))=='98722242bc05b6187ef2ab1568a79562b72c45f060e10933ae40bc132f39f7fa'
owner_run=json.loads(git(PUBLIC+'run.json'))
independent_run=json.loads((BASE/(PREFIX+'-run.json')).read_text())
for k in ['id','head_sha','status','conclusion']:
    assert owner_run[k]==independent_run[k],k
files=[('original-connector-job.log',official),('complete-environment-inventory.json',(BASE/(PREFIX+'-inventory.json')).read_bytes()),('DeclarationAudit-actual.log',o['DeclarationAudit']),('DeclarationAudit-reconstructed.lean',(BASE/(PREFIX+'-DeclarationAudit.lean')).read_bytes()),('CompleteEnvironmentAudit-reconstructed.lean',(BASE/(PREFIX+'-CompleteEnvironmentAudit.lean')).read_bytes()),('NaturalPastCompleteObservation-actual.log',o['NaturalPastCompleteObservation']),('HybridSizeCore-actual.log',o['HybridSizeCore']),('RationalResidualCertificate-actual.log',o['RationalResidualCertificate'])]
checks=[]
for name,data in files:
    assert git(PUBLIC+name)==data,name
    checks.append({'path':PUBLIC+name,'sha256':sha(data),'bytes':len(data),'byte_equal':True})
comparison=json.loads(git(PUBLIC+'prior-owned-row-comparison.json'))
ind=json.loads((BASE/(PREFIX+'-independent.json')).read_text())
assert len(artifacts)==68
assert comparison['prior_owned_rows']==4188 and comparison['all_prior_rows_byte_identical']
assert comparison['changed_rows']==[] and comparison['missing_rows']==[]
assert len(comparison['added_rows'])==21 and comparison['added_rows']==ind['new_owned_rows']
timing=json.loads(git(PUBLIC+'runtime-timing.json'))
owner_jobs=json.loads(git(PUBLIC+'jobs.json'))['jobs']
assert len(owner_jobs)==1
owner_job=owner_jobs[0]
for key in ['id','name','status','conclusion']:
    assert owner_job[key]==json.loads((BASE/(PREFIX+'-job.json')).read_text())[key]
serial=next(step for step in owner_job['steps'] if step['name']=='Verify G6 frozen sources serially')
def seconds(start,end):return (datetime.fromisoformat(end.replace('Z','+00:00'))-datetime.fromisoformat(start.replace('Z','+00:00'))).total_seconds()
assert timing['job_started_at']==owner_job['started_at'] and timing['job_completed_at']==owner_job['completed_at']
assert timing['job_elapsed_seconds']==seconds(owner_job['started_at'],owner_job['completed_at'])==768
assert timing['serial_step_started_at']==serial['started_at'] and timing['serial_step_completed_at']==serial['completed_at']
assert timing['serial_step_elapsed_seconds']==seconds(serial['started_at'],serial['completed_at'])==736
categories={'custom':0.0,'cache':0.0,'audit':0.0}
for command in r:
    label=Path(command['argv'][-1]).stem
    category='cache' if command['argv'][1:3]!=['env','lean'] else 'audit' if label in ['DeclarationAudit','CompleteEnvironmentAudit'] else 'custom'
    categories[category]+=seconds(command['start'],command['end'])
for category,total in categories.items():assert abs(total-timing[category+'_command_seconds'])<1e-6
result={'author_commit':AUTHOR,'original_connector_log_sha256':sha(official),'original_connector_log_byte_equal':True,'input_manifest_equal':True,'all182_receipts_equal':True,'all181_noncache_stdout_byte_equal':correspondence,'all_saved_author_actual_stdout_files':saved_stdout_checks,'empty_Hybrid_output_exact':True,'attributed_V2_parser_byte_preserved':True,'rejected_and_corrected_static_normalization_record':transport,'actual_terminal_run_key_fields_equal':True,'author_artifact_count':len(artifacts),'author_artifacts_authenticated':artifacts,'exact_data_files':checks,'author_prior_row_comparison_preserved':comparison,'independent_all4188prior_rows_exact':ind['all_prior4188_rows_byte_equal'],'source_and_complete_audits_independently_reconstructed':True,'archive_download_attempted':False,'author_REST_job_and_actual_receipt_timing_authenticated':timing,'compiler_invoked':False}
(BASE/(PREFIX+'-author-correspondence.json')).write_text(json.dumps(result,indent=2)+'\n')
ind['author_publication_commit']=AUTHOR
ind['author_correspondence_file']=PREFIX+'-author-correspondence.json'
ind['author_exact_data_files']=checks
(BASE/(PREFIX+'-independent.json')).write_text(json.dumps(ind,indent=2)+'\n')
print(json.dumps({'author_commit':AUTHOR,'artifacts':len(artifacts),'receipts':182,'noncache_stdout':181,'exact_data_files':len(checks),'raw_sha256':checks[1]['sha256'],'prior4188_rows_exact':True,'new_rows':21}))
