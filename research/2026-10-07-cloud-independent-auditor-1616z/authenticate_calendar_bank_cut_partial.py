"""Authenticate actual scalar-bank and deterministic-cut PASS with failed probabilistic-cut consumers; no compiler."""
from pathlib import Path
import base64,collections,gzip,hashlib,json,re,subprocess
BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[1]
FROZEN='01e367686a9d2e9d0b67611ab762a8f39cd0f49c'
AUTHOR='1ec76a6fdba645c7188ce46571495ccf6bb3fc90'
PREFIX='calendar-bank-cut-37699267727'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
def git(path,commit=FROZEN): return subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)
log=(BASE/(PREFIX+'-actions.log')).read_bytes()
text=log.decode()
assert 'RUNTIME_SMOKE_PASSED source_commit='+FROZEN in text
assert 'Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)' in text
assert 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550' in text
assert '5114a5b2e77fa40336ddd9491ebc5f04e767a5c299b7ebdd637104b1f96d2758' in text
msgs=[re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?','',l.split('\t',2)[-1].lstrip('\ufeff')) for l in text.splitlines() if '\tVerify G6 frozen sources serially\t' in l]
inputs=next(json.loads(m.split(' ',1)[1]) for m in msgs if m.startswith('G6_INPUTS '))
assert inputs['source_commit']==FROZEN and len(inputs['modules'])==165
prior=json.loads((BASE/'calendar-banks-37695092891-independent.json').read_text())
changed={'UnifiedLean.G6.AncestralRateFree','UnifiedLean.G6.RateBankCommon','UnifiedLean.G6.InheritanceBankCommon'}
old={r['module']:r for r in prior['source_checks'] if r['module'] not in changed}
newpins={'UnifiedLean.G6.AncestralRateFree':'8d772b5fa71e3fef61d073b72bb4c56e89d5179468a774ed511a4c0aec5d3291','UnifiedLean.G6.RateBankCommon':'c61cc8b9dc4e87b3346ac03f6acf81132bb72803be86a49c3d75928232114c3e','UnifiedLean.G6.InheritanceBankCommon':'ded7cf8d347b2fe966e0ae52a4421b1118b12d259096b63c883a51797042493a','ActualCutTagRefinement':'c39df8d6fc98edfa1acd9dd1042bedb4bacde08c85e26b69acf019b451b9dea8','ActualCutJointLaw':'e8d5e316cdd84147574c5f12d4a61d50c323a94a4bb70509b954cbba4a339f18','ActualCalendarCutContext':'9af74be4362938df964da969df95beb23c058ef3131d0e29200a9afca2c0d3b2','ActualFiniteCutJointLaw':'6ff13aac1e2209078661664f7567a18453c54a0a27d48ef1cd95d44e3cd518fe','ActualCalendarEndpointHistory':'3128992426a7ac45c735e3fc806f24263131f7da73cedf56359eddd4ceee030d','ActualObservationCutRefinement':'aa0086b7b65eb3788fe0038a0a7708fec9e17fe64c8582a4b5243b2771a44195'}
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
    checks.append({'module':module,'sha256':record['sha256'],'source':found,'matched_frozen_git_source':True,'matched_previous_159_source':module in old})
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
assert pending is None and len(receipts)==164 and sum(r['exit']==0 for r in receipts)==163
assert all(b['matches_receipt'] for b in blocks if b['label']!='cache')
failed={b['label'] for b in blocks if b['exit']}
assert failed=={'ActualCutJointLaw'}
excluded={'ActualCutJointLaw','ActualCalendarCutContext','ActualFiniteCutJointLaw','ActualCalendarEndpointHistory','ActualObservationCutRefinement'}
assert all(m not in outputs for m in excluded-{'ActualCutJointLaw'})
assert all(m in outputs for m in ['AncestralRateFree','RateBankCommon','InheritanceBankCommon','UpperRateSourceCommon','ActualCutTagRefinement'])
for n in sorted(failed):
    assert b'error:' in outputs[n]
    (BASE/(PREFIX+'-FAIL-'+n+'.log')).write_bytes(outputs[n])
audit=outputs['DeclarationAudit'].decode()
reports=[]
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",audit,re.DOTALL):
    ax=[x.strip() for x in (m.group(2) or '').split(',') if x.strip()]
    assert set(ax)<={'propext','Classical.choice','Quot.sound'}
    reports.append({'name':m.group(1),'axioms':ax})
assert len(reports)==len({r['name'] for r in reports})==305
assert all(r in reports for r in prior['selected_reports']) and 'sorryAx' not in audit
receipt=next(json.loads(m.split(' ',1)[1]) for m in msgs if m.startswith('G6_COMPLETE_ENVIRONMENT_PAYLOAD '))
begin=msgs.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN');end=msgs.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END')
lines=msgs[begin+1:end]
interleave=[l for l in lines if not re.fullmatch(r'[A-Za-z0-9+/]+={0,2}',l)]
compressed=base64.b64decode(''.join(l for l in lines if l not in interleave),validate=True)
raw=gzip.decompress(compressed)
assert len(raw)==receipt['bytes']==5826377
assert sha(raw)==receipt['sha256']=='eb35261af203a7f98ede7eb53ab78a7d325e30d290e6f3d26d61971e6bb530c1'
prior_inventory=json.loads(gzip.decompress((BASE/'calendar-banks-37695092891-inventory.json.gz').read_bytes()))
inv=json.loads(raw)
assert not inv['owned_axioms'] and not inv['nonstandard_axiom_rows'] and not inv['missing_modules']
assert inv['declaration_count']==len(inv['declarations'])==3902
assert inv['theorem_declaration_count']==sum(r['kind']=='theorem' for r in inv['declarations'])==2542
owned=[m for m in inputs['topological_order'] if m not in excluded]
assert len(owned)==receipt['selected_custom_modules']==160 and inv['selected_modules']==owned
assert set(r['module'] for r in inv['declarations'])==set(owned)
assert len({r['name'] for r in inv['declarations']})==3902
current_rows={r['name']:r for r in inv['declarations']}
assert all(r['name'] in current_rows for r in reports)
newreports=[r['name'] for r in reports if r['name'] not in {x['name'] for x in prior['selected_reports']}]
assert len(newreports)==63 and all(n.startswith(('UnifiedLean.G6.AncestralRateFree.','UnifiedLean.G6.RateBankCommon.','UnifiedLean.G6.InheritanceBankCommon.','UnifiedLean.G6.UpperRateSourceCommon.','CloudG3.ActualCutTagRefinement.')) for n in newreports)
for module,n,t in [('UnifiedLean.G6.AncestralRateFree',20,16),('UnifiedLean.G6.RateBankCommon',38,35),('UnifiedLean.G6.InheritanceBankCommon',13,13),('UnifiedLean.G6.UpperRateSourceCommon',17,16),('ActualCutTagRefinement',19,14)]:
    rows=[r for r in inv['declarations'] if r['module']==module]
    assert len(rows)==n and sum(r['kind']=='theorem' for r in rows)==t
assert all(current_rows[r['name']]==r for r in prior_inventory['declarations'])
for module,n,t in [('UnifiedLean.G6.ResidualProgram',75,57)]:
    rows=[r for r in inv['declarations'] if r['module']==module]
    assert len(rows)==n and sum(r['kind']=='theorem' for r in rows)==t
assert all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} and isinstance(r['type_references'],list) and isinstance(r['body_references'],list) for r in inv['declarations'])
template=git('research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean').decode()
assert sha(template.encode())==inputs['dependencies']['complete_inventory_template_sha256']
oldnames='#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'
assert template.count(oldnames)==1
template=template.replace(oldnames,'#['+', '.join(json.dumps(n) for n in owned)+']')
audit_source=('\n'.join('import '+n for n in owned)+'\n'+template).encode()
assert sha(audit_source)==receipt['audit_source_sha256']
helper=git('research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/complete_environment.py')
assert sha(helper)==inputs['dependencies']['complete_inventory_helper_sha256']
assert next(b for b in blocks if b['label']=='CompleteEnvironmentAudit')['matches_receipt']
publicbase='research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/evidence/g6-run-37699267727-FAILED/'
public=[]
if AUTHOR is not None:
    author_log=git(publicbase+'actions.log',AUTHOR)
    # Author transports raw connector/job logs; independently fetched gh step log has other prefixes.
    author_messages=[re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?','',l.split('\t',2)[-1].lstrip('\ufeff')) for l in author_log.decode().splitlines()]
    author_inputs=next(json.loads(m.split(' ',1)[1]) for m in author_messages if m.startswith('G6_INPUTS '))
    author_receipts=[json.loads(m.split(' ',1)[1]) for m in author_messages if m.startswith('G6_RECEIPT ')]
    assert author_inputs==inputs and author_receipts==receipts
    public.append({'path':publicbase+'actions.log','sha256':sha(author_log),'independently_fetched_gh_log_sha256':sha(log),'whole_log_byte_equal':author_log==log,'all_command_receipts_and_input_manifest_equal':True,'different_transport':'author connector-job prefix versus gh step prefixes'})
    for name,data in [('complete-environment-inventory.json',raw),('DeclarationAudit-actual.log',outputs['DeclarationAudit']),('CompleteEnvironmentAudit-reconstructed.lean',audit_source)]+[(n+'-actual.log',outputs[n]) for n in sorted(failed|{'AncestralRateFree','RateBankCommon','InheritanceBankCommon','UpperRateSourceCommon','ActualCutTagRefinement','CompleteCalendarJointLaw'})]:
        published=git(publicbase+name,AUTHOR);assert published==data,name
        public.append({'path':publicbase+name,'sha256':sha(data),'byte_equal':True})
run=json.loads((BASE/(PREFIX+'-run.json')).read_text())
assert run['headSha']==FROZEN and run['status']=='completed' and run['conclusion']=='failure'
(BASE/(PREFIX+'-inventory.json.gz')).write_bytes(compressed)
(BASE/(PREFIX+'-CompleteEnvironmentAudit.lean')).write_bytes(audit_source)
(BASE/(PREFIX+'-final-audit.txt')).write_bytes(outputs['DeclarationAudit'])
result={'schema':'independent-bank-pass-deterministic-cut-pass-probabilistic-cut-failed-v1','run':run,'log_sha256':sha(log),'command_receipts':164,'zero_exit_commands':163,'custom_modules':165,'successful_custom_modules':160,'failed_custom_modules':sorted(failed),'blocked_custom_modules':sorted(excluded-{'ActualCutJointLaw'}),'excluded_custom_modules':sorted(excluded),'source_checks':checks,'command_stdout_checks':blocks,'selected_reports':reports,'selected_report_count':305,'selected_report_counts':{'G6':226,'G3':64,'G5':15},'final_audit_sha256':sha(outputs['DeclarationAudit']),'complete_inventory_receipt':receipt,'complete_inventory_kind_counts':dict(collections.Counter(r['kind'] for r in inv['declarations'])),'complete_inventory_module_counts':dict(collections.Counter(r['module'] for r in inv['declarations'])),'complete_inventory_each_module_owned_rows':True,'all_successful_custom_modules_owned_and_compiled':True,'all_target_modules_accepted':False,'non_payload_interleaved_stderr':interleave,'author_publication_commit':AUTHOR,'author_readback_checks':public,'runtime_smoke_and_version_binary_source_pins_present':True,'prior_independent_receipt':'calendar-banks-37695092891-independent.json','all_prior_3795_owned_rows_byte_equal':True,'newly_accepted_modules':['UnifiedLean.G6.AncestralRateFree','UnifiedLean.G6.RateBankCommon','UnifiedLean.G6.InheritanceBankCommon','UnifiedLean.G6.UpperRateSourceCommon','ActualCutTagRefinement'],'compiler_launched_by_auditor':False}
(BASE/(PREFIX+'-independent.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['command_receipts','zero_exit_commands','custom_modules','successful_custom_modules','failed_custom_modules','blocked_custom_modules','selected_report_count','complete_inventory_receipt','non_payload_interleaved_stderr']}))
