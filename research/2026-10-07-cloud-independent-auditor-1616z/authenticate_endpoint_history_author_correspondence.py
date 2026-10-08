"""Authenticate saved author/official terminal correspondence and reconstruct named audit; no compiler."""
from pathlib import Path
import json,re,hashlib,subprocess,gzip
BASE=Path(__file__).resolve().parent; ROOT=BASE.parents[1]
PREFIX='endpoint-history-attempt-37713030087'; AUTHOR='a367763b978e298497403b65d3052fdcb24ac491'
FROZEN='9caec2d7309fb8c5bc249b213e76f43eee5fc738'
PUBLIC='research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/evidence/g6-run-37713030087-FAILED/'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(path,commit=AUTHOR):return subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)
def messages(raw,official=False):
    lines=raw.decode().splitlines()
    return [re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?','',l.split('\t',2)[-1].lstrip('\ufeff')) for l in lines]
def extract(ms):
    inputs=next(json.loads(m.split(' ',1)[1]) for m in ms if m.startswith('G6_INPUTS '))
    rs=[];out={};pending=None;lines=[]
    for m in ms:
        if m.startswith('G6_COMMAND '):assert pending is None;pending=json.loads(m.split(' ',1)[1]);lines=[]
        elif m.startswith('G6_RECEIPT '):
            assert pending is not None;r=json.loads(m.split(' ',1)[1]);label=Path(r['argv'][-1]).stem if r['argv'][1:3]==['env','lean'] else 'cache'
            out[label]=('\n'.join(lines)+('\n' if lines else '')).encode();rs.append(r);pending=None
        elif pending is not None:lines.append(m)
    assert pending is None;return inputs,rs,out
official=(BASE/(PREFIX+'-actions.log')).read_bytes();author=git(PUBLIC+'actions.log')
i,rs,out=extract(messages(official,True));ai,ars,aout=extract(messages(author))
assert i==ai and rs==ars and len(rs)==167
assert len(out)==167
correspondence=[]
for label,raw in out.items():
    if label=='cache':continue
    assert aout[label]==raw,label
    correspondence.append({'label':label,'stdout_sha256':sha(raw),'byte_equal':True})
assert len(correspondence)==166
ind=json.loads((BASE/(PREFIX+'-independent.json')).read_text())
checks={r['module']:r for r in ind['source_checks']}
excluded=set(ind['excluded_custom_modules'])
targets=[l.strip() for l in git('research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/targets.txt',FROZEN).decode().splitlines() if l.strip() and not l.lstrip().startswith('#')]
passed=[m for m in targets if m not in excluded];decl=[]
for m in passed:
    source=git(checks[m]['source'],FROZEN).decode();namespace=re.search(r'^namespace\s+(\S+)\s*$',source,re.M)[1]
    decl.extend(namespace+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_']+)",source,re.M))
assert len(decl)==344 and decl==[r['name'] for r in ind['selected_reports']]
named=('\n'.join('import '+m for m in passed)+'\n\n'+'\n'.join('#print axioms '+n for n in decl)+'\n').encode()
assert named==git(PUBLIC+'DeclarationAudit-reconstructed.lean')
(BASE/(PREFIX+'-DeclarationAudit.lean')).write_bytes(named)
raw=gzip.decompress((BASE/(PREFIX+'-inventory.json.gz')).read_bytes())
checks_public=[]
for name,data in [('complete-environment-inventory.json',raw),('DeclarationAudit-actual.log',out['DeclarationAudit']),('DeclarationAudit-reconstructed.lean',named),('CompleteEnvironmentAudit-reconstructed.lean',(BASE/(PREFIX+'-CompleteEnvironmentAudit.lean')).read_bytes())]+[(n+'-actual.log',out[n]) for n in ['ActualCalendarCutContext','ActualFiniteCutJointLaw','ActualCalendarEndpointHistory']]:
    assert git(PUBLIC+name)==data,name
    checks_public.append({'path':PUBLIC+name,'sha256':sha(data),'byte_equal':True})
result={'author_commit':AUTHOR,'official_log_sha256':sha(official),'author_log_sha256':sha(author),'whole_log_equal':official==author,'cache_equality_claimed':False,'input_manifest_equal':True,'all167_command_receipts_equal':True,'all166_noncache_stdout_byte_equal':correspondence,'named_audit_reconstructed_directly_from_frozen_targets_and_successful_sources':True,'named_audit_source_sha256':sha(named),'complete_inventory_and_audit_and_selected_module_logs_byte_equal':checks_public,'archive_transport_attempted':False,'compiler_invoked':False}
(BASE/(PREFIX+'-author-correspondence.json')).write_text(json.dumps(result,indent=2)+'\n')
ind['author_publication_commit']=AUTHOR;ind['author_readback_checks']=checks_public;ind['author_official_correspondence_file']=PREFIX+'-author-correspondence.json';ind['named_audit_source_sha256']=sha(named)
(BASE/(PREFIX+'-independent.json')).write_text(json.dumps(ind,indent=2)+'\n')
print(json.dumps({'author_commit':AUTHOR,'command_receipts_equal':len(rs),'noncache_stdout_equal':len(correspondence),'named_audit_declarations':len(decl),'named_audit_source_sha256':sha(named),'inventory_bytes':len(raw),'inventory_sha256':sha(raw)}))
