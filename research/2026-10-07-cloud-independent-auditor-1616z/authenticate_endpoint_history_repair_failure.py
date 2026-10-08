"""Authenticate endpoint-history repair failure and unchanged full successful selection and complete successful selection; no compiler."""
from pathlib import Path
import base64,collections,gzip,hashlib,json,re,subprocess
BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[1]
FROZEN='9caec2d7309fb8c5bc249b213e76f43eee5fc738'
AUTHOR='a367763b978e298497403b65d3052fdcb24ac491'
PREFIX='endpoint-history-attempt-37713030087'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
def git(path,commit=FROZEN): return subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)
log=(BASE/(PREFIX+'-actions.log')).read_bytes()
text=log.decode()
assert 'RUNTIME_SMOKE_PASSED source_commit='+FROZEN in text
assert 'Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)' in text
assert 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550' in text
assert '5114a5b2e77fa40336ddd9491ebc5f04e767a5c299b7ebdd637104b1f96d2758' in text
msgs=[re.sub(r'^\ufeff?\d{4}-\d\d-\d\dT\S+Z ?','',l.split('\t',2)[-1].lstrip('\ufeff')) for l in text.splitlines()]
inputs=next(json.loads(m.split(' ',1)[1]) for m in msgs if m.startswith('G6_INPUTS '))
assert inputs['source_commit']==FROZEN and len(inputs['modules'])==165
prior=json.loads((BASE/'finite-cut-attempt-37710655968-independent.json').read_text())
changed={'ActualCalendarEndpointHistory'}
old={r['module']:r for r in prior['source_checks'] if r['module'] not in changed}
newpins={'ActualCalendarEndpointHistory':'d6a2be33078a71362f0b86bf052185d84d66f2da17bc008a852a28dfd17ed257'}
# Locate exact immutable source bytes; duplicate historical copies are harmless when byte-identical.
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',FROZEN],cwd=ROOT).decode().splitlines()
checks=[]
for module,record in inputs['modules'].items():
    if module in old: assert record['sha256']==old[module]['sha256'],module
    else: assert record['sha256']==newpins[module],module
    candidates=[p for p in paths if p.endswith('/'+record['path'])]
    own='research/2026-10-07-cloud-g6-sol-ultra-1601z/sources/'+record['path']
    candidates.sort(key=lambda p:(p!=own,len(p),p))
    found=None
    for p in candidates:
        raw=git(p)
        if sha(raw)==record['sha256']: found=p;break
    assert found,module
    checks.append({'module':module,'sha256':record['sha256'],'source':found,'matched_frozen_git_source':True,'matched_previous_165_source':module in old})
receipts=[];blocks=[];outputs={};pending=None;out=[]
for m in msgs:
    if m.startswith('G6_COMMAND '):
        assert pending is None;pending=json.loads(m.split(' ',1)[1]);out=[]
    elif m.startswith('G6_RECEIPT '):
        assert pending is not None
        r=json.loads(m.split(' ',1)[1]);raw=('\n'.join(out)+('\n' if out else '')).encode()
        label=Path(r['argv'][-1]).stem if r['argv'][1:3]==['env','lean'] else 'cache'
        blocks.append({'label':label,'exit':r['exit'],'stdout_sha256':sha(raw),'matches_receipt':sha(raw)==r['output_sha256']})
        outputs[label]=raw;receipts.append(r);pending=None
    elif pending is not None: out.append(m)
assert pending is None and len(receipts)==167 and sum(r['exit']==0 for r in receipts)==166
assert all(b['matches_receipt'] for b in blocks if b['label']!='cache')
failed={b['label'] for b in blocks if b['exit']}
assert failed=={'ActualCalendarEndpointHistory'}
excluded={'ActualCalendarEndpointHistory','ActualObservationCutRefinement'}
assert all(m not in outputs for m in excluded-{'ActualCalendarEndpointHistory'})
assert all(m in outputs for m in ['ActualCutJointLaw','ActualCalendarCutContext','ActualFiniteCutJointLaw'])
for n in sorted(failed):
    assert b'error:' in outputs[n]
    (BASE/(PREFIX+'-FAIL-'+n+'.log')).write_bytes(outputs[n])
audit=outputs['DeclarationAudit'].decode()
reports=[]
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",audit,re.DOTALL):
    ax=[x.strip() for x in (m.group(2) or '').split(',') if x.strip()]
    assert set(ax)<={'propext','Classical.choice','Quot.sound'}
    reports.append({'name':m.group(1),'axioms':ax})
assert len(reports)==len({r['name'] for r in reports})==344
assert all(r in reports for r in prior['selected_reports']) and 'sorryAx' not in audit
receipt=next(json.loads(m.split(' ',1)[1]) for m in msgs if m.startswith('G6_COMPLETE_ENVIRONMENT_PAYLOAD '))
begin=msgs.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN');end=msgs.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END')
lines=msgs[begin+1:end]
interleave=[l for l in lines if not re.fullmatch(r'[A-Za-z0-9+/]+={0,2}',l)]
compressed=base64.b64decode(''.join(l for l in lines if l not in interleave),validate=True)
raw=gzip.decompress(compressed)
assert len(raw)==receipt['bytes']==5962385
assert sha(raw)==receipt['sha256']=='57c0911a5a317f183e15539be8c0753c7b391bc3b335ad98195214aab249402e'
prior_inventory=json.loads(gzip.decompress((BASE/'finite-cut-attempt-37710655968-inventory.json.gz').read_bytes()))
inv=json.loads(raw)
assert not inv['owned_axioms'] and not inv['nonstandard_axiom_rows'] and not inv['missing_modules']
assert inv['declaration_count']==len(inv['declarations'])==3965
assert inv['theorem_declaration_count']==sum(r['kind']=='theorem' for r in inv['declarations'])==2589
owned=[m for m in inputs['topological_order'] if m not in excluded]
assert len(owned)==receipt['selected_custom_modules']==163 and inv['selected_modules']==owned
assert set(r['module'] for r in inv['declarations'])==set(owned)
assert len({r['name'] for r in inv['declarations']})==3965
current_rows={r['name']:r for r in inv['declarations']}
assert all(r['name'] in current_rows for r in reports)
newreports=[r['name'] for r in reports if r['name'] not in {x['name'] for x in prior['selected_reports']}]
assert not newreports and reports==prior['selected_reports']
assert all(r['name'] in current_rows and current_rows[r['name']]==r for r in prior_inventory['declarations'])
context_rows=[r for r in inv['declarations'] if r['module']=='ActualFiniteCutJointLaw']
assert len(context_rows)==9 and sum(r['kind']=='theorem' for r in context_rows)==7
rows=[r for r in inv['declarations'] if r['module']=='ActualCutJointLaw']
assert len(rows)==10 and sum(r['kind']=='theorem' for r in rows)==5
assert all(current_rows[r['name']]==r for r in prior_inventory['declarations'])
for module,n,t in [('UnifiedLean.G6.ResidualProgram',75,57)]:
    rows=[r for r in inv['declarations'] if r['module']==module]
    assert len(rows)==n and sum(r['kind']=='theorem' for r in rows)==t
assert all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} and isinstance(r['type_references'],list) and isinstance(r['body_references'],list) for r in inv['declarations'])
template=git('research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean').decode()
assert sha(template.encode())==inputs['dependencies']['complete_inventory_template_sha256']
assert raw==gzip.decompress((BASE/'finite-cut-attempt-37710655968-inventory.json.gz').read_bytes())
oldnames='#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'
assert template.count(oldnames)==1
template=template.replace(oldnames,'#['+', '.join(json.dumps(n) for n in owned)+']')
audit_source=('\n'.join('import '+n for n in owned)+'\n'+template).encode()
assert sha(audit_source)==receipt['audit_source_sha256']
helper=git('research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/complete_environment.py')
assert sha(helper)==inputs['dependencies']['complete_inventory_helper_sha256']
assert next(b for b in blocks if b['label']=='CompleteEnvironmentAudit')['matches_receipt']
publicbase='research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/evidence/g6-run-37713030087-FAILED/'
public=[]
if AUTHOR is not None:
    author_log=git(publicbase+'actions.log',AUTHOR)
    # Author transports raw connector/job logs; independently fetched gh step log has other prefixes.
    author_messages=[re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?','',l.split('\t',2)[-1].lstrip('\ufeff')) for l in author_log.decode().splitlines()]
    author_inputs=next(json.loads(m.split(' ',1)[1]) for m in author_messages if m.startswith('G6_INPUTS '))
    author_receipts=[json.loads(m.split(' ',1)[1]) for m in author_messages if m.startswith('G6_RECEIPT ')]
    assert author_inputs==inputs and author_receipts==receipts
    public.append({'path':publicbase+'actions.log','sha256':sha(author_log),'independently_fetched_gh_log_sha256':sha(log),'whole_log_byte_equal':author_log==log,'all_command_receipts_and_input_manifest_equal':True,'different_transport':'author connector-job prefix versus gh step prefixes'})
    for name,data in [('complete-environment-inventory.json',raw),('DeclarationAudit-actual.log',outputs['DeclarationAudit']),('CompleteEnvironmentAudit-reconstructed.lean',audit_source)]+[(n+'-actual.log',outputs[n]) for n in sorted(failed|{'ActualCutJointLaw','ActualCalendarCutContext','ActualFiniteCutJointLaw'})]:
        published=git(publicbase+name,AUTHOR);assert published==data,name
        public.append({'path':publicbase+name,'sha256':sha(data),'byte_equal':True})
run=json.loads((BASE/(PREFIX+'-run.json')).read_text())
assert run['head_sha']==FROZEN and run['status']=='completed' and run['conclusion']=='failure'
(BASE/(PREFIX+'-inventory.json.gz')).write_bytes(compressed)
(BASE/(PREFIX+'-CompleteEnvironmentAudit.lean')).write_bytes(audit_source)
(BASE/(PREFIX+'-final-audit.txt')).write_bytes(outputs['DeclarationAudit'])
result={'schema':'independent-endpoint-history-repair-failure-unchanged-selection-v1','run':run,'log_sha256':sha(log),'command_receipts':167,'zero_exit_commands':166,'custom_modules':165,'successful_custom_modules':163,'failed_custom_modules':sorted(failed),'blocked_custom_modules':sorted(excluded-{'ActualCalendarEndpointHistory'}),'excluded_custom_modules':sorted(excluded),'source_checks':checks,'command_stdout_checks':blocks,'selected_reports':reports,'selected_report_count':344,'selected_report_counts':{'G6':226,'G3':103,'G5':15},'final_audit_sha256':sha(outputs['DeclarationAudit']),'complete_inventory_receipt':receipt,'complete_inventory_kind_counts':dict(collections.Counter(r['kind'] for r in inv['declarations'])),'complete_inventory_module_counts':dict(collections.Counter(r['module'] for r in inv['declarations'])),'complete_inventory_each_module_owned_rows':True,'all_successful_custom_modules_owned_and_compiled':True,'all_target_modules_accepted':False,'non_payload_interleaved_stderr':interleave,'author_publication_commit':AUTHOR,'author_readback_checks':public,'runtime_smoke_and_version_binary_source_pins_present':True,'prior_independent_receipt':'finite-cut-attempt-37710655968-independent.json','all_prior_3965_owned_rows_byte_equal':True,'newly_accepted_modules':[],'compiler_launched_by_auditor':False}
(BASE/(PREFIX+'-independent.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['command_receipts','zero_exit_commands','custom_modules','successful_custom_modules','failed_custom_modules','blocked_custom_modules','selected_report_count','complete_inventory_receipt','non_payload_interleaved_stderr']}))
