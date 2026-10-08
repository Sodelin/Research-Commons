"""Read-only source, DAG, terminal and budget authentication; never executes Lean or Actions."""
import ast, datetime, hashlib, json, re, subprocess
from pathlib import Path
G=['git','--git-dir=/workspace/research-commons/.git']
PREP='c20be64e9a2d4ce458e4d55844c7b0b56b6cf923'
CURRENT='b46adf28c4334d54124e6d813e3c72253d028649'
ACTUAL='ceadcd149cd3a7f093853815cad2489b91380ba7'
AUTHOR='6a1966832b799620223e2ba7c4ecd908c074d1a8'
PRIMARY='22118e7a3a058097934377a6da0c3fd72edcaa51'
ROOT='research/2026-10-07-cloud-g6-sol-ultra-1601z/'
BASE=ROOT+'verification/evidence/g6-run-37743712528-FAILED/'
PACKET=ROOT+'verification/preparation/finite-corruption-direction-repair-0750z/'
PLAN=ROOT+'verification/freeze-plans/finite-corruption-direction-repair-static.json'
FAIL='UnifiedLean.G6.FiniteCorruptionBoundary'
BLOCK='ActualObservationCorruption'
def sha(b): return hashlib.sha256(b).hexdigest()
def get(ref,path):
    b=subprocess.check_output(G+['show',ref+':'+path])
    blob=subprocess.check_output(G+['rev-parse',ref+':'+path],text=True).strip()
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
    return b,blob
def js(ref,path): return json.loads(get(ref,path)[0])
raw,planblob=get(PREP,PLAN);p=json.loads(raw)
assert sha(raw)=='a508944db6ced8339c45f97b3be6b53ebfe992c926ab66154af0439cd8523eda'
old=js(ACTUAL,ROOT+'verification/freeze-plans/finite-observation-actual179-static.json')
a=js(AUTHOR,BASE+'inputs-recovered.json')
audit=js(AUTHOR,BASE+'axiom-audit-recovered.json')
owned=js(AUTHOR,BASE+'complete-ownership-receipt.json')
receipts=js(AUTHOR,BASE+'receipts-recovered.json')
timing=js(AUTHOR,BASE+'runtime-timing.json')
prior=js('cdf4c4c0f9e0f6de59a7701b14656565a84cc481',ROOT+'verification/evidence/g6-run-37738512508-PASS/inputs-recovered.json')
assert a['source_commit']==p['prior_verified_input']==ACTUAL
assert p['prior_actual_run']==37743712528 and p['prior_actual_receipt_commit']==AUTHOR
assert len(receipts)==183 and sum(r['exit']==0 for r in receipts)==182
assert [r['argv'][-1].split('/')[-1] for r in receipts if r['exit']!=0]==['FiniteCorruptionBoundary.lean']
assert len(audit['named_declarations'])==p['prior_actual_named']==501
assert len(owned['all_owned_counts_by_module'])==p['prior_actual_custom']==179
assert set(owned['all_owned_counts_by_module'])==set(prior['modules'])
assert not {FAIL,BLOCK} & set(owned['all_owned_counts_by_module'])
assert not owned['owned_axioms'] and not owned['nonstandard_axiom_rows'] and not owned['missing_modules']
assert not audit['unexpected_axioms'] and not audit['missing_reports']
inventory,ib=get(AUTHOR,BASE+'complete-environment-inventory.json')
assert inventory==get('cdf4c4c0f9e0f6de59a7701b14656565a84cc481',ROOT+'verification/evidence/g6-run-37738512508-PASS/complete-environment-inventory.json')[0]
inv=json.loads(inventory)
assert sha(inventory)==p['prior_actual_inventory_sha256']=='cf0a500c9e35831cd598d6f12edd4fc0e63b534a2ad4322eb6584981307944ba'
assert inv['declaration_count']==p['prior_actual_complete_owned']==4209
assert owned['all_owned_counts_by_kind']['theorem']==p['prior_actual_complete_theorems']==2766
assert p['actual_runtime_dependencies']==a['dependencies']==old['actual_runtime_dependencies']
runner=get(ACTUAL,ROOT+'verification/run.py')[0]
assert sha(runner)==a['dependencies']['verification_script_sha256']
tree=ast.parse(runner.decode());node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='lean_imports')
ns={'re':re};exec(compile(ast.Module(body=[node],type_ignores=[]),'<pinned import parser ONLY>','exec'),ns)
imports=ns['lean_imports'];checks=[];source={}
repair=p['attributed_repair'];candidate,cb=get(PREP,repair['candidate_copy'])
assert get(repair['author_root_commit'],repair['author_repository_path'])==(candidate,cb)
assert sha(candidate)==repair['author_sha256']=='6b5964de36b9cc4f2e79d4d7e8652498b8f2517e98769c1b9aa6938bf197754a' and len(candidate)==4697
for name,im in a['modules'].items():
    m=p['modules'][name];om=old['modules'][name]
    actual,ab=get(ACTUAL,om['repository_path']);current,nb=get(CURRENT,om['repository_path'])
    assert actual==current and ab==nb and sha(actual)==im['sha256']==om['sha256']
    assert imports(actual.decode())==im['imports']==om['imports']
    assert om['repository_path'].endswith('/'+im['path'])
    if name==FAIL:
        assert {k:v for k,v in m.items() if k!='sha256'}=={k:v for k,v in om.items() if k!='sha256'}
        assert m['sha256']==sha(candidate)
        assert sha(actual)==repair['original_failed_sha256']=='25d5afd4e2032613539d5d0d39308d4eff98d642ae8eaec361a4f3f5db3edbcf'
        assert actual.count(b'Finset.sum_div')==2
        assert candidate==actual.replace(b'Finset.sum_div',b'\xe2\x86\x90 Finset.sum_div')
        source[name]=candidate
    else:
        assert m==om
        if name in prior['modules']: assert im==prior['modules'][name]
        source[name]=actual
    checks.append(dict(module=name,sha256=sha(actual),blob=ab,bytes=len(actual),accepted=name in prior['modules']))
assert len(checks)==181 and sum(x['accepted'] for x in checks)==179
assert p['changed_source_count']==1 and p['all_other_requested_sources_fixed']==180
assert p['unchanged_accepted_custom_modules']==179 and p['new_modules']==p['new_module_original_and_copy_pins']==[]
assert p['replaced_failed_module']==FAIL and p['unchanged_blocked_module']==BLOCK
assert sha(source[BLOCK])=='201fe29b7efb33277625da5515cd5659f8f60a471c91d86b366c303ba55fc754'
diff,db=get(PREP,PACKET+'unified.diff')
assert diff==get(repair['author_root_commit'],'research/2026-10-08-cloud-finite-corruption-direction-repair-0746z/FiniteCorruptionBoundary.diff')[0]
assert sha(diff)==repair['diff_sha256']=='01b7b092d451daf487231802ae3ba725e9e3e01523cf15b34c2d528ffeb22672'
assert len(diff)==841
for key in ['targets','topological_order','named_counts','named_total','namespace_counts','mathlib_roots','lean_roots','external_context_sha256','controls']:
    assert p[key]==old[key]
assert p['targets']==a['targets'] and p['topological_order']==a['topological_order']
assert p['named_counts']==dict(audit['module_counts'],**{FAIL:10,BLOCK:2})
assert sum(p['named_counts'].values())==p['named_total']==513 and p['namespace_counts']=={'G6':364,'G3':134,'G5':15}
order=[];seen=set();external=set();lean=set();active=set()
def visit(n):
    if n.startswith('Mathlib.'): external.add(n);return
    if n.startswith(('Lean.','Std.','Init.')): lean.add(n);return
    assert n not in active,'cycle '+n
    if n in seen:return
    assert n in p['modules'],'missing '+n
    active.add(n)
    for dep in imports(source[n].decode()):visit(dep)
    active.remove(n);seen.add(n);order.append(n)
for n in p['targets']:visit(n)
assert order==p['topological_order'] and order[:179]==prior['topological_order']
assert len(seen)==len(p['modules'])==p['custom_modules']==181 and len(p['targets'])==47
assert sorted(external)==p['mathlib_roots']==a['mathlib_roots'] and len(external)==68
assert sorted(lean)==p['lean_roots'] and len(lean)==1
assert p['external_root_addition']==[]
for c in p['controls']:
    b,blob=get(ACTUAL,c['repository_path'])
    assert get(CURRENT,c['repository_path'])==(b,blob)
    assert blob==c['git_blob_sha'] and sha(b)==c['sha256'] and len(b)==c['bytes']
assert len(p['controls'])==6
api=js(PREP,PACKET+'API-INPUTS.json')
assert subprocess.check_output(['git','-C','/workspace/g6-build/deps/mathlib','rev-parse','HEAD'],text=True).strip()==api['pinned_mathlib_commit']==a['dependencies']['mathlib_commit']
field=Path('/workspace/g6-build/deps/mathlib/Mathlib/Algebra/BigOperators/Field.lean').read_bytes()
assert sha(field)==api['source_sha256'] and len(field)==api['source_bytes']==2002
assert 'lemma Finset.sum_div' in field.decode()
assert sha(Path('/workspace/g6-runtime/lean-4.33.1-linux/bin/lean').read_bytes())==a['dependencies']['lean_executable_sha256']
failedlog,flb=get(AUTHOR,BASE+'FiniteCorruptionBoundary-actual.log')
assert sha(failedlog)==api['actual_failure_stdout_sha256']=='be2d9c58cdb57baa0e493bd88022c1ff161a8c5cdc7b5395f06dbebc90c0736f' and len(failedlog)==2126
b=p['runtime_budget'];dt=lambda s:datetime.datetime.fromisoformat(s.replace('Z','+00:00'))
assert b['actual_prior_job_seconds']==timing['actual_job_seconds']==764==(dt(timing['job_completed_at'])-dt(timing['job_started_at'])).total_seconds()
assert b['actual_prior_serial_seconds']==timing['actual_serial_step_seconds']==736
assert b['estimated_job_seconds']==764+b['changed_plus_blocked_source_reserve_seconds']+b['additional_audit_reserve_seconds']+b['variation_reserve_seconds']==894
assert b['changed_plus_blocked_source_reserve_seconds']==20 and b['additional_audit_reserve_seconds']==10 and b['variation_reserve_seconds']==100
assert b['job_cap_seconds']==900 and b['command_cap_seconds']==180
assert '--trust=0 -j1 -M4096' in b['status']
for r in receipts[1:]:assert r['argv'][3:6]==['--trust=0','-j1','-M4096']
f=next(r for r in receipts if r['exit']!=0)
assert f['output_sha256']==sha(failedlog) and (dt(f['end'])-dt(f['start'])).total_seconds()==timing['failed_finite_boundary_seconds']==3.116196
packet_checks=[]
paths=subprocess.check_output(G+['ls-tree','-r','--name-only',PREP,PACKET],text=True).splitlines()+[PLAN]
assert len(paths)==10
for path in paths:
    value,blob=get(PREP,path);assert get(CURRENT,path)==(value,blob)
    packet_checks.append(dict(path=path,sha256=sha(value),blob=blob,bytes=len(value)))
primary_files=['FINITE-OBSERVATION-ACTUAL181-RETAINED179-FAILURE-REVIEW.md','FINITE-CORRUPTION-DIRECTION-REPAIR-SOURCE-SELECTION-REVIEW.md']
primary_hashes=['21adda30047c185bff03d475687c9ca14fdef4da79dc7c6fe9ea5f92e37a653d','b59b272ac66a123d425b0523a11146b89de1f51a0e9ef4bf0e2d8e32f54defdf']
remote=json.loads(Path('/workspace/root-repair-primary-remote-read.json').read_text());primaries=[]
for name,h,r in zip(primary_files,primary_hashes,remote):
    path='research/2026-10-07-cloud-independent-auditor-1616z/'+name
    value,blob=get(PRIMARY,path);assert get(CURRENT,path)==(value,blob)
    assert sha(value)==h and r['content'].encode()==value and r['sha']==blob
    primaries.append(dict(commit=PRIMARY,path=path,sha256=h,blob=blob,bytes=len(value)))
result=dict(status='ROOT STATIC AUTHENTICATION PASS; separate fresh ONE gate required',current_source_head=CURRENT,prior_frozen_input=ACTUAL,actual_receipt=AUTHOR,primary_reviews=primaries,prep=PREP,plan_path=PLAN,plan_sha256=sha(raw),plan_blob=planblob,all181_requested_sources=checks,all179_successful_sources_exact=True,all180_other_requested_sources_exact=True,repair=dict(**repair,blob=cb,bytes=len(candidate)),acyclic_complete_DAG=True,custom=181,named=513,targets=47,complete_inventory_exact=True,inventory=dict(sha256=sha(inventory),blob=ib,bytes=len(inventory),owned=4209,theorems=2766),packet_files=packet_checks,controls=p['controls'],actual_dependencies=a['dependencies'],api=api,runtime_budget=b,compiler_invoked=False,actions_polled=False,launch_authorized=False)
Path('/workspace/root-finite181-direction-auth.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','plan_sha256','custom','named','targets','compiler_invoked','launch_authorized']}))
