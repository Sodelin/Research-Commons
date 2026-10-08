"""Independent byte/DAG/budget authentication only; never invokes Lean or Actions."""
import ast, datetime, hashlib, json, re, subprocess
from pathlib import Path
G=['git','--git-dir=/workspace/research-commons/.git']
PREP='f6c18f8dee6ffbbd80d04df237e1fc767ceca37d'
CURRENT='b6776d019c813066458f9f292f5307ae4545016e'
ACTUAL='62e937a2b58f00f6ed1197133650b6da2f96f71f'
AUTHOR='cdf4c4c0f9e0f6de59a7701b14656565a84cc481'
ROOT='research/2026-10-07-cloud-g6-sol-ultra-1601z/'
BASE=ROOT+'verification/evidence/g6-run-37738512508-PASS/'
PACKET=ROOT+'verification/preparation/finite-observation-actual179-0702z/'
PLAN=ROOT+'verification/freeze-plans/finite-observation-actual179-static.json'
def sha(b): return hashlib.sha256(b).hexdigest()
def get(ref,path):
    b=subprocess.check_output(G+['show',ref+':'+path])
    blob=subprocess.check_output(G+['rev-parse',ref+':'+path],text=True).strip()
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
    return b,blob
def js(ref,path): return json.loads(get(ref,path)[0])
raw,planblob=get(PREP,PLAN);p=json.loads(raw)
assert sha(raw)=='897902afd0c20ad4b896e58b056ae2ab721af404131231fca5da5b90a57a5489'
a=js(AUTHOR,BASE+'inputs-recovered.json')
old=js(ACTUAL,ROOT+'verification/freeze-plans/rational-zero-flag-actual178-repair-static.json')
audit=js(AUTHOR,BASE+'axiom-audit-recovered.json')
inventory=js(AUTHOR,BASE+'complete-environment-inventory.json')
owned=js(AUTHOR,BASE+'complete-ownership-receipt.json')
receipts=js(AUTHOR,BASE+'receipts-recovered.json')
timing=js(AUTHOR,BASE+'runtime-timing.json')
assert a['source_commit']==p['prior_verified_input']==ACTUAL
assert len(a['modules'])==p['prior_actual_custom']==179
assert len(receipts)==182 and all(r['exit']==0 for r in receipts)
assert len(audit['named_declarations'])==p['prior_actual_named']==501
assert inventory['declaration_count']==p['prior_actual_complete_owned']==4209
assert sha(get(AUTHOR,BASE+'complete-environment-inventory.json')[0])==p['prior_actual_inventory_sha256']
assert p['actual_runtime_dependencies']==a['dependencies']
runner=get(ACTUAL,ROOT+'verification/run.py')[0]
assert sha(runner)==a['dependencies']['verification_script_sha256']
tree=ast.parse(runner.decode());node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='lean_imports')
ns={'re':re};exec(compile(ast.Module(body=[node],type_ignores=[]),'<pinned import parser ONLY>','exec'),ns)
imports=ns['lean_imports'];checks=[];source={}
for name,im in a['modules'].items():
    m=p['modules'][name];assert m==old['modules'][name]
    actual,ab=get(ACTUAL,m['repository_path']);current,cb=get(CURRENT,m['repository_path'])
    assert actual==current and ab==cb and sha(actual)==im['sha256']==m['sha256']
    assert imports(actual.decode())==im['imports']==m['imports']
    assert m['repository_path'].endswith('/'+im['path'])
    assert name in owned['all_owned_counts_by_module']
    source[name]=actual;checks.append(dict(module=name,**m,blob=ab,bytes=len(actual)))
assert len(checks)==p['unchanged_accepted_custom_modules']==179
newchecks=[]
for pin in p['new_module_original_and_copy_pins']:
    b,blob=get(PREP,pin['staged_path']);original,ob=get(pin['original_commit'],pin['original_path'])
    assert b==original and blob==ob==pin['git_blob_sha']
    assert sha(b)==pin['sha256'] and len(b)==pin['bytes']
    m=p['modules'][pin['module']];assert m['repository_path']==pin['future_formal_path']
    assert m['sha256']==sha(b) and m['imports']==imports(b.decode())
    # New formal paths must remain absent before the owner freeze.
    assert subprocess.run(G+['cat-file','-e',CURRENT+':'+pin['future_formal_path']],stderr=subprocess.DEVNULL).returncode!=0
    namespace=re.search(r'^namespace\s+(\S+)\s*$',b.decode(),re.M)[1]
    names=[namespace+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_']+)",b.decode(),re.M)]
    printed=re.findall(r'^#print axioms (\S+)',b.decode(),re.M)
    assert names==pin['selected_names_actual_runner'] and len(names)==pin['selected_count']==p['named_counts'][pin['module']]
    assert printed==pin['printed_names'] and len(printed)==pin['printed_count']
    assert not re.search(r'\b(?:sorry|axiom)\s',re.sub(r'/-[\s\S]*?-/', '', b.decode()))
    source[pin['module']]=b;newchecks.append(pin)
assert len(newchecks)==2 and sum(x['selected_count'] for x in newchecks)==12
assert sum(x['printed_count'] for x in newchecks)==10
assert p['targets'][:45]==a['targets']==old['targets']
assert p['targets'][45:]==p['new_modules']==[x['module'] for x in newchecks]
order=[];seen=set();external=set();lean=set();active=set()
def visit(n):
    if n.startswith('Mathlib.'): external.add(n);return
    if n.startswith(('Lean.','Std.','Init.')): lean.add(n);return
    assert n not in active,'dependency cycle '+n
    if n in seen:return
    assert n in p['modules'],'missing '+n
    active.add(n)
    for dep in p['modules'][n]['imports']:visit(dep)
    active.remove(n);seen.add(n);order.append(n)
for n in p['targets']:visit(n)
assert order==p['topological_order'] and order[:179]==a['topological_order']
assert len(seen)==len(p['modules'])==p['custom_modules']==181 and len(p['targets'])==47
assert sorted(external)==p['mathlib_roots']==a['mathlib_roots']==old['mathlib_roots'] and len(external)==68
assert sorted(lean)==p['lean_roots']==old['lean_roots'] and len(lean)==1
assert p['external_context_sha256']==old['external_context_sha256'] and p['external_root_addition']==[]
assert p['named_counts']==dict(audit['module_counts'],**{x['module']:x['selected_count'] for x in newchecks})
assert sum(p['named_counts'].values())==p['named_total']==513 and p['namespace_counts']=={'G6':364,'G3':134,'G5':15}
controls=[]
for c in p['controls']:
    b,blob=get(ACTUAL,c['repository_path']);now,nb=get(CURRENT,c['repository_path'])
    assert b==now and blob==nb==c['git_blob_sha'] and sha(b)==c['sha256'] and len(b)==c['bytes']
    controls.append(c)
assert len(controls)==6
api=js(PREP,PACKET+'API-INPUTS.json')
assert subprocess.check_output(['git','-C','/workspace/g6-build/deps/mathlib','rev-parse','HEAD'],text=True).strip()==a['dependencies']['mathlib_commit']
for pin in api['mathlib']:
    b=Path('/workspace/g6-build/deps/mathlib',pin['path']).read_bytes()
    assert sha(b)==pin['sha256'] and len(b)==pin['bytes']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==pin['git_blob_sha']
for pin in api['provider_pins']:
    b=source[pin['module']];assert sha(b)==pin['sha256'] and len(b)==pin['bytes']
    assert p['modules'][pin['module']]['imports']==pin['imports']
assert sha(Path('/workspace/g6-runtime/lean-4.33.1-linux/bin/lean').read_bytes())==a['dependencies']['lean_executable_sha256']
budget=p['runtime_budget'];b=budget;dt=lambda s:datetime.datetime.fromisoformat(s.replace('Z','+00:00'))
assert b['actual179_job_seconds']==timing['job_elapsed_seconds']==768
assert b['actual179_serial_seconds']==timing['serial_step_elapsed_seconds']==736
assert b['planning_total_seconds']==768+2*10+10+100==898<900
assert b['job_cap_seconds']==900 and b['per_command_cap_seconds']==180 and b['flags']==['--trust=0','-j1','-M4096']
comparable=[]
for c in b['comparable_actual_receipts']:
    matches=[r for r in receipts if r['argv'][-1].split('/')[-1]==c['source']];assert len(matches)==1
    r=matches[0];assert c['start']==r['start'] and c['end']==r['end'] and c['exit']==r['exit']==0
    assert c['stdout_sha256']==r['output_sha256'] and c['elapsed_seconds']==(dt(r['end'])-dt(r['start'])).total_seconds()
    stdout,_=get(AUTHOR,BASE+c['source'].removesuffix('.lean')+'-actual.log')
    assert sha(stdout)==c['stdout_sha256'];comparable.append(c)
assert len(comparable)==6
for r in receipts[1:]:assert r['argv'][3:6]==['--trust=0','-j1','-M4096']
canon=p['prior_independent_acceptance'];craw,cb=get(canon['commit'],canon['path'])
assert sha(craw)==canon['sha256'] and get(CURRENT,canon['path'])[0]==craw
source_review=js(PREP,PACKET+'SOURCE-PINS.json')['source_review']
sr,sb=get(source_review['commit'],source_review['path']);assert sha(sr)==source_review['sha256']
packet_checks=[]
paths=subprocess.check_output(G+['ls-tree','-r','--name-only',PREP,PACKET],text=True).splitlines()+[PLAN]
assert len(paths)==10
for path in paths:
    b,blob=get(PREP,path);assert get(CURRENT,path)==(b,blob)
    packet_checks.append(dict(path=path,sha256=sha(b),blob=blob,bytes=len(b)))
primary=dict(commit='b6776d019c813066458f9f292f5307ae4545016e',path='research/2026-10-07-cloud-independent-auditor-1616z/FINITE-OBSERVATION-ACTUAL179-181-SOURCE-SELECTION-REVIEW.md',sha256='385c4666de34722ddf91c6c074e35de81f8cd93dd534cf3204f5a6c3f9a4ce15')
pr,pb=get(primary['commit'],primary['path']);assert sha(pr)==primary['sha256']
assert get(CURRENT,primary['path'])[0]==pr
result=dict(primary_selection=dict(**primary,blob=pb,bytes=len(pr)),status='ROOT STATIC AUTHENTICATION PASS with matching primary source/selection; separate ONE gate required',actual179=ACTUAL,actual_receipt=AUTHOR,current_source_head=CURRENT,prep=PREP,plan_path=PLAN,plan_sha256=sha(raw),plan_blob=planblob,all179_exact=checks,new_sources=newchecks,packet_files=packet_checks,custom=181,named=513,targets=47,all179_order_imports_roots_fixed=True,acyclic_complete_DAG=True,controls=controls,provider_api_pins=api,runtime_budget=budget,comparable_receipts_authenticated=comparable,canonical179=dict(**canon,blob=cb),source_review=dict(**source_review,blob=sb),compiler_invoked=False,actions_polled=False,launch_authorized=False)
Path('/workspace/root-actual179-finite-observation-auth.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','plan_sha256','custom','named','targets','compiler_invoked','launch_authorized']}))
