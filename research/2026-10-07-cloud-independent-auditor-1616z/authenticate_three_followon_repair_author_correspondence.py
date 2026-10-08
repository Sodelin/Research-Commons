"""Compare preserved author artifacts to independently retrieved terminal bytes; no compiler."""
from pathlib import Path
import hashlib, json, re, subprocess, sys

BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[1]
PREFIX='three-followon-repair-37734981680'
AUTHOR=sys.argv[1]
PUBLIC='research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/evidence/g6-run-37734981680-FAILED/'
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
empty=json.loads(git(PUBLIC+'empty-stdout-reconstruction.json'))
assert empty['module']=='HybridSizeCore' and empty['actual_compiler_output_bytes']==0
assert empty['actual_compiler_output_sha256']==sha(o['HybridSizeCore']) and o['HybridSizeCore']==b''
assert empty['all181_noncache_actual_stdout_hashes_match'] and not empty['source_or_command_or_receipt_changed']
assert sha(git(PUBLIC+empty['parser_path']))==empty['parser_sha256']
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
assert len(artifacts)==67
assert comparison['prior_owned_rows_unchanged']==4158 and comparison['new_owned_rows']==30
assert comparison['changed_prior_rows']==[] and comparison['missing_prior_rows']==[]
assert comparison['new_owned_rows']==30 and comparison['new_rows']==ind['new_owned_rows']
result={'author_commit':AUTHOR,'original_connector_log_sha256':sha(official),'original_connector_log_byte_equal':True,'input_manifest_equal':True,'all182_receipts_equal':True,'all181_noncache_stdout_byte_equal':correspondence,'all_saved_author_actual_stdout_files':saved_stdout_checks,'empty_stdout_reconstruction_preserved':empty,'actual_terminal_run_key_fields_equal':True,'author_artifact_count':len(artifacts),'author_artifacts_authenticated':artifacts,'exact_data_files':checks,'author_prior_row_comparison_preserved':comparison,'independent_all4158prior_rows_exact':ind['all_prior4158_rows_byte_equal'],'source_and_complete_audits_independently_reconstructed':True,'archive_download_attempted':False,'compiler_invoked':False}
(BASE/(PREFIX+'-author-correspondence.json')).write_text(json.dumps(result,indent=2)+'\n')
ind['author_publication_commit']=AUTHOR
ind['author_correspondence_file']=PREFIX+'-author-correspondence.json'
ind['author_exact_data_files']=checks
(BASE/(PREFIX+'-independent.json')).write_text(json.dumps(ind,indent=2)+'\n')
print(json.dumps({'author_commit':AUTHOR,'artifacts':len(artifacts),'receipts':182,'noncache_stdout':181,'exact_data_files':len(checks),'raw_sha256':checks[1]['sha256'],'prior4158_rows_exact':True,'new_rows':30}))
