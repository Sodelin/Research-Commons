import hashlib,json,re,subprocess
from pathlib import Path
G=['git','--git-dir=/workspace/research-commons/.git']
PREP='3fb8ad532e2f9f3d22f9c6dc22571000d0807366'
CURRENT='6841981bd70d46de665b3a5a95b7e2b9cc121903'
ACTUAL='00863f04f69c8c97857d97c5ca63f1511019e366'
AUTHOR='6529c3b8346c7ecfd48c4b9e2a9dfd17002d87d3'
ROOT='research/2026-10-07-cloud-g6-sol-ultra-1601z/'
BASE=ROOT+'verification/evidence/g6-run-37734981680-FAILED/'
PLAN=ROOT+'verification/freeze-plans/rational-zero-flag-actual178-repair-static.json'
OLDPLAN=ROOT+'verification/freeze-plans/two-followon-actual177-repair-static.json'
def get(ref,path):
    raw=subprocess.check_output(G+['show',ref+':'+path]);blob=subprocess.check_output(G+['rev-parse',ref+':'+path],text=True).strip()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blob
    return raw,blob
def sha(raw):return hashlib.sha256(raw).hexdigest()
def js(ref,path):return json.loads(get(ref,path)[0])
raw,blob=get(PREP,PLAN);p=json.loads(raw);old=js(ACTUAL,OLDPLAN)
inputs=js(AUTHOR,BASE+'inputs-recovered.json');receipt=js(AUTHOR,BASE+'complete-ownership-receipt.json')
assert sha(raw)=='5de11dd729ef2f6190daf8c5153b8fb9b741a691d706e4525377958dfce83521'
assert inputs['source_commit']==ACTUAL
assert len(p['modules'])==len(inputs['modules'])==p['custom_modules']==179
assert p['targets']==inputs['targets']==old['targets'] and len(p['targets'])==45
assert p['topological_order']==inputs['topological_order']==old['topological_order']
for key in ['mathlib_roots','lean_roots','named_counts','named_total','namespace_counts','external_context_sha256','external_root_addition']:
    assert p[key]==old[key],key
assert p['mathlib_roots']==inputs['mathlib_roots'] and len(p['mathlib_roots'])==68
assert p['named_total']==sum(p['named_counts'].values())==501
repair=set(p['repair_modules']);assert repair=={'UnifiedLean.G6.RationalResidualCertificate'}
assert len(receipt['all_owned_counts_by_module'])==178 and repair.isdisjoint(receipt['all_owned_counts_by_module'])
checks=[]
for name,im in inputs['modules'].items():
    before=old['modules'][name];after=p['modules'][name]
    assert before['sha256']==im['sha256'] and before['imports']==im['imports']
    assert before['repository_path'].endswith('/'+im['path'])
    assert before['repository_path']==after['repository_path'] and before['imports']==after['imports']
    actual,ab=get(ACTUAL,before['repository_path']);current,cb=get(CURRENT,before['repository_path'])
    assert actual==current and ab==cb and sha(actual)==before['sha256']
    if name not in repair:
        assert before==after and name in receipt['all_owned_counts_by_module']
        checks.append(dict(module=name,path=before['repository_path'],sha256=sha(actual),blob=cb))
assert len(checks)==p['unchanged_accepted_custom_modules']==178
pin=p['repair_pins']['UnifiedLean.G6.RationalResidualCertificate']
oldraw,ob=get(ACTUAL,pin['formal_path']);newraw,nb=get(PREP,pin['candidate_path']);diff,db=get(PREP,pin['diff_path'])
assert sha(oldraw)==pin['old_sha256'] and sha(newraw)==pin['candidate_sha256'] and len(newraw)==pin['candidate_bytes']==7170
assert sha(diff)==pin['diff_sha256']=='357ebd8552c12eb7f9b75ed1ad4b972e82cb288d634f185f5f050fcfc3183a41'
needle=b'    simp only [rationalResidualCount, hk, hz, if_true, if_false,'
assert oldraw.count(needle)==1
assert oldraw.replace(needle,needle+b' Nat.zero_le,',1)==newraw
assert p['modules']['UnifiedLean.G6.RationalResidualCertificate']['sha256']==sha(newraw)
names=lambda s:re.findall(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+(\S+)',s.decode(),re.M)
assert names(oldraw)==names(newraw) and len(names(newraw))==p['named_counts']['UnifiedLean.G6.RationalResidualCertificate']
start=b'lemma rationalResidualCount_sum';end=b'lemma rationalDenominator_real'
assert oldraw[oldraw.index(start):oldraw.index(end)]==newraw[newraw.index(start):newraw.index(end)]
api=pin['pinned_api'];prelude=Path(api['local_runtime_source']).read_bytes()
assert sha(prelude)==api['source_sha256']
assert api['declaration'].encode() in prelude and prelude.decode().splitlines()[1931].startswith('theorem Nat.zero_le')
assert sha(Path('/workspace/g6-runtime/lean-4.33.1-linux/bin/lean').read_bytes())==api['lean_executable_sha256']
diagnostic,logblob=get(AUTHOR,BASE+'RationalResidualCertificate-actual.log')
assert diagnostic.count('⊢ ↑(if 0 ≤ K'.encode())==2
assert diagnostic.count(b':115:67: error: unsolved goals')==1
b=p['runtime_budget'];assert b['planning_total_seconds']==635+30+10+100==775
assert b['job_cap_seconds']==900 and b['per_command_cap_seconds']==180 and b['flags']==['--trust=0','-j1','-M4096']
controls=[]
for path in [ROOT+'verification/verify.sh',ROOT+'verification/run.py','.github/workflows/g6-cloud-lean.yml']:
    a,ab=get(ACTUAL,path);c,cb=get(CURRENT,path);assert a==c and ab==cb
    controls.append(dict(path=path,sha256=sha(c),blob=cb))
canon=p['prior_independent_acceptance'];cr,cb=get(canon['commit'],canon['path']);assert sha(cr)==canon['sha256']
primary=dict(commit='6e13682ed61231d445a6370ef631f9e7b9a18662',path='research/2026-10-07-cloud-independent-auditor-1616z/RATIONAL-ZERO-FLAG-ACTUAL178-SOURCE-SELECTION-REVIEW.md',sha256='33ffcb107f12f2c7d7e262378a15eaaf257abaab3127db0c24deab6766553621')
pr,pb=get(primary['commit'],primary['path']);assert sha(pr)==primary['sha256']
assert get(CURRENT,primary['path'])[0]==pr
result=dict(status='ROOT STATIC ONE-SOURCE AUTHENTICATION PASS; matching primary selection and separate root ONE gate required',prep=PREP,actual_input=ACTUAL,author=AUTHOR,plan_path=PLAN,plan_sha256=sha(raw),plan_blob=blob,all178_successful_sources_exact=checks,requested_sources=179,requested_named=501,repair=dict(module=pin['module'],path=pin['candidate_path'],sha256=sha(newraw),blob=nb,bytes=len(newraw),names=names(newraw),diff_sha256=sha(diff),sum_rfl_unchanged=True,only_added_Nat_zero_le=True),diagnostic=dict(path=BASE+'RationalResidualCertificate-actual.log',sha256=sha(diagnostic),blob=logblob,two_zero_flags_confirmed=True),pinned_api=api,targets_imports_paths_order_external_roots_fixed=True,controls=controls,budget=b,canonical178=canon,compiler_invoked=False,launch_authorized=False)
Path('/workspace/root-actual178-rational-auth.json').write_text(json.dumps(result,indent=2)+'\n')
result['current_source_head']=CURRENT
result['primary_selection']=dict(**primary,blob=pb)
result['status']='ROOT STATIC ONE-SOURCE AUTHENTICATION PASS with matching canonical178 and primary selection; separate ONE gate required'
Path('/workspace/root-actual178-rational-auth.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','plan_sha256','requested_sources','requested_named','compiler_invoked','launch_authorized']}))
