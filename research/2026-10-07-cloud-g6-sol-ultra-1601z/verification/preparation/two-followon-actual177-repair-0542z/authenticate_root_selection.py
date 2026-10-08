import hashlib,json,re,subprocess,difflib
from pathlib import Path
G=['git','--git-dir=/workspace/research-commons/.git']
PREP='852463f6e690330ab789f694ca2e4ce57b83aa6a';ACTUAL='73f7fda44fa43f293a9ab46774560f2b029f9758';AUTHOR='0066fe52e73e5c1a1a07fab1a1e1e6688d9eaf73';HEAD='b06b623c730330a50db5fd8b21eb31a138e99d9d'
ROOT='research/2026-10-07-cloud-g6-sol-ultra-1601z/';BASE=ROOT+'verification/evidence/g6-run-37731710313-FAILED/'
PLAN=ROOT+'verification/freeze-plans/two-followon-actual177-repair-static.json';OLDPLAN=ROOT+'verification/freeze-plans/three-reviewed-followon-actual176-static.json'
def get(ref,path):
 raw=subprocess.check_output(G+['show',ref+':'+path]);blob=subprocess.check_output(G+['rev-parse',ref+':'+path],text=True).strip()
 assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blob
 return raw,blob
def js(ref,path):return json.loads(get(ref,path)[0])
def sha(raw):return hashlib.sha256(raw).hexdigest()
raw,blob=get(PREP,PLAN);p=json.loads(raw);old=js(ACTUAL,OLDPLAN);inputs=js(AUTHOR,BASE+'inputs-recovered.json');receipt=js(AUTHOR,BASE+'complete-ownership-receipt.json')
assert sha(raw)=='c8c55ecc312deb0b4c3577d85225b31ab87acced40c3f8b77cf503ecbde79395'
assert inputs['source_commit']==ACTUAL
assert len(p['modules'])==len(inputs['modules'])==p['custom_modules']==179
assert p['targets']==inputs['targets']==old['targets'] and p['topological_order']==inputs['topological_order']==old['topological_order']
for key in ['mathlib_roots','lean_roots','named_counts','named_total','namespace_counts','external_context_sha256','external_root_addition']:
 assert p[key]==old[key],key
assert p['named_total']==sum(p['named_counts'].values())==501
repair=set(p['repair_modules']);assert repair=={'HybridSizeCore','UnifiedLean.G6.RationalResidualCertificate'}
assert len(receipt['all_owned_counts_by_module'])==177
assert repair.isdisjoint(receipt['all_owned_counts_by_module'])
checks=[]
for name,input_module in inputs['modules'].items():
 before=old['modules'][name]
 after=p['modules'][name]
 assert before['sha256']==input_module['sha256'] and before['imports']==input_module['imports']
 assert before['repository_path'].endswith('/'+input_module['path'])
 assert before['repository_path']==after['repository_path'] and before['imports']==after['imports']
 rawOld,oldblob=get(ACTUAL,before['repository_path']);current,nowblob=get(HEAD,before['repository_path'])
 assert rawOld==current and oldblob==nowblob and sha(rawOld)==before['sha256']
 if name not in repair:
  assert before==after and name in receipt['all_owned_counts_by_module']
  checks.append(dict(module=name,path=before['repository_path'],sha256=sha(rawOld),blob=nowblob))
assert len(checks)==p['unchanged_accepted_custom_modules']==177
derivatives=[]
for name,pin in p['repair_pins'].items():
 oldraw,ob=get(ACTUAL,pin['formal_path']);newraw,nb=get(PREP,pin['candidate_path']);diff,db=get(PREP,pin['diff_path'])
 assert sha(oldraw)==pin['old_sha256'] and sha(newraw)==pin['candidate_sha256'] and len(newraw)==pin['candidate_bytes'] and sha(diff)==pin['diff_sha256']
 assert p['modules'][name]['sha256']==sha(newraw)
 if name=='HybridSizeCore':
  assert newraw.replace(b'noncomputable def cellT',b'def cellT',1)==oldraw
 else:
  expected=oldraw.decode().replace('    exact div_nonneg (by positivity) hU\n  unfold rationalResidualCount\n  by_cases hk : k ≤ K <;> by_cases hz : k = 0 <;>\n    simp only [hk, hz, if_true, if_false] <;> positivity', '    exact div_nonneg (mul_nonneg (by norm_num) hnext) hU\n  unfold rationalResidualCount\n  apply add_nonneg\n  · split_ifs\n    · exact div_nonneg hT hU\n    · exact le_rfl\n  · split_ifs\n    · exact herror\n    · exact le_rfl').replace('  simp [rationalResidualCount, rationalDenominator, rationalTerm_real,\n    rationalPrefix_real, rationalError_real, ha]', '  by_cases hk : k ≤ K <;> by_cases hz : k = 0 <;>\n    simp only [rationalResidualCount, hk, hz, if_true, if_false,\n      Rat.cast_add, Rat.cast_div, Rat.cast_zero, rationalTerm_real,\n      rationalDenominator_real, rationalError_real, ha]')
  assert expected.encode()==newraw
  def sumproof(s):return s[s.index(b'lemma rationalResidualCount_sum'):s.index(b'lemma rationalDenominator_real')]
  assert sumproof(oldraw)==sumproof(newraw)
 names=re.findall(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+(\S+)',newraw.decode(),re.M)
 assert len(names)==p['named_counts'][name] and names==re.findall(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+(\S+)',oldraw.decode(),re.M)
 derivatives.append(dict(module=name,path=pin['candidate_path'],sha256=sha(newraw),blob=nb,bytes=len(newraw),names=names,diff_sha256=sha(diff),sum_rfl_unchanged=name!='HybridSizeCore'))
b=p['runtime_budget'];assert b['planning_total_seconds']==727+30+10+100==867 and b['job_cap_seconds']==900 and b['per_command_cap_seconds']==180 and b['flags']==['--trust=0','-j1','-M4096']
controls=[]
for path in [ROOT+'verification/verify.sh',ROOT+'verification/run.py','.github/workflows/g6-cloud-lean.yml']:
 a,ab=get(ACTUAL,path);c,cb=get(HEAD,path);assert a==c and ab==cb
 controls.append(dict(path=path,sha256=sha(c),blob=cb))
primary_path='research/2026-10-07-cloud-independent-auditor-1616z/TWO-FOLLOWON-ACTUAL177-PROOF-REPAIR-SOURCE-SELECTION-REVIEW.md'
primary,pb=get(HEAD,primary_path)
assert sha(primary)=='9b09f07f077592e0b730c43d6273b926c8852dfba37542acd67583ded71c7245'
canon_path='research/2026-10-07-cloud-independent-auditor-1616z/THREE-FOLLOWON-177-COMPLETE-VERIFIED-PARTIAL-REVIEW.md'
canon,cb=get('48d318b09136550347c43196f8e90d46ca2cef11',canon_path)
assert sha(canon)=='0160eb585548f35af00d6e58a05b934193eb9a6bc21262ba5d23b0e1ae11f181'
result=dict(status='ROOT STATIC TWO-SOURCE AUTHENTICATION PASS with matching canonical177 and primary repair-selection; launch requires separate root gate',prep=PREP,actual_input=ACTUAL,author=AUTHOR,current_source_head=HEAD,plan_path=PLAN,plan_sha256=sha(raw),plan_blob=blob,all177_successful_sources_exact=checks,requested_sources=179,requested_named=501,repairs=derivatives,targets_imports_paths_order_external_roots_fixed=True,controls=controls,budget=b,primary_selection=dict(commit=HEAD,path=primary_path,sha256=sha(primary),blob=pb),canonical177=dict(commit='48d318b09136550347c43196f8e90d46ca2cef11',path=canon_path,sha256=sha(canon),blob=cb),compiler_invoked=False,launch_authorized=False)
Path('/workspace/root-actual177-repair-auth.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','plan_sha256','requested_sources','requested_named','compiler_invoked','launch_authorized']}))
