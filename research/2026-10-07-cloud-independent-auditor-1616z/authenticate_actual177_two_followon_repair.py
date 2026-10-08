"""Read-only Git/source/selection authentication. Does not invoke Lean."""
from pathlib import Path
import difflib,hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[2]
BASE=Path(__file__).resolve().parent
G6='research/2026-10-07-cloud-g6-sol-ultra-1601z'
PREP=G6+'/verification/preparation/two-followon-actual177-repair-0542z'
COMMIT='852463f6e690330ab789f694ca2e4ce57b83aa6a'
ACTUAL='73f7fda44fa43f293a9ab46774560f2b029f9758'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(c,p): return subprocess.check_output(['git','show',c+':'+p],cwd=ROOT)
def record(c,p):
 b=git(c,p)
 return {'commit':c,'path':p,'bytes':len(b),'sha256':sha(b),'git_blob':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
pins=json.loads(git(COMMIT,PREP+'/SOURCE-PINS.json'))
planpath=G6+'/verification/freeze-plans/two-followon-actual177-repair-static.json'
plan=json.loads(git(COMMIT,planpath))
assert sha(git(COMMIT,planpath))==pins['static_plan_sha256']=='c8c55ecc312deb0b4c3577d85225b31ab87acced40c3f8b77cf503ecbde79395'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',COMMIT,PREP],cwd=ROOT).decode().splitlines()+[planpath]
assert len(paths)==8
artifacts=[record(COMMIT,p) for p in paths]
for p in paths: assert (ROOT/p).read_bytes()==git(COMMIT,p),p
changes=[]
for m,r in pins['changes'].items():
 old=git(ACTUAL,r['formal_path']).decode()
 new=git(COMMIT,r['candidate_path']).decode()
 assert sha(old.encode())==r['old_sha256'] and sha(new.encode())==r['candidate_sha256']
 assert len(new.encode())==r['candidate_bytes']
 d=git(COMMIT,r['diff_path'])
 assert sha(d)==r['diff_sha256']
 expected=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=r['formal_path']+'@73f7fda',tofile=r['candidate_path']))
 assert expected.encode()==d
 if m=='HybridSizeCore':
  assert old.replace('def cellT (p q u v : ℝ) : ℝ :=','noncomputable def cellT (p q u v : ℝ) : ℝ :=',1)==new
 else:
  a='''    exact div_nonneg (by positivity) hU
  unfold rationalResidualCount
  by_cases hk : k ≤ K <;> by_cases hz : k = 0 <;>
    simp only [hk, hz, if_true, if_false] <;> positivity'''
  b='''    exact div_nonneg (mul_nonneg (by norm_num) hnext) hU
  unfold rationalResidualCount
  apply add_nonneg
  · split_ifs
    · exact div_nonneg hT hU
    · exact le_rfl
  · split_ifs
    · exact herror
    · exact le_rfl'''
  a2='''  simp [rationalResidualCount, rationalDenominator, rationalTerm_real,
    rationalPrefix_real, rationalError_real, ha]'''
  b2='''  by_cases hk : k ≤ K <;> by_cases hz : k = 0 <;>
    simp only [rationalResidualCount, hk, hz, if_true, if_false,
      Rat.cast_add, Rat.cast_div, Rat.cast_zero, rationalTerm_real,
      rationalDenominator_real, rationalError_real, ha]'''
  assert old.count(a)==old.count(a2)==1
  assert old.replace(a,b).replace(a2,b2)==new
  def sumproof(t): return t[t.index('lemma rationalResidualCount_sum'):t.index('lemma rationalDenominator_real')]
  assert sumproof(old)==sumproof(new)
 changes.append({'module':m,'old':record(ACTUAL,r['formal_path']),'candidate':record(COMMIT,r['candidate_path']),'diff':record(COMMIT,r['diff_path']),'exhaustive_transform':True})
prior=json.loads(git('8cd0359fe0cc87cdaa942d9635f90ab0148abc18',G6+'/verification/freeze-plans/three-reviewed-followon-actual176-static.json'))
fixed=['targets','custom_modules','mathlib_roots','lean_roots','topological_order','named_counts','named_total','namespace_counts','external_context_sha256','external_root_addition']
for k in fixed: assert plan[k]==prior[k],k
changed=[]
for m,r in prior['modules'].items():
 if r!=plan['modules'][m]:
  assert {k for k in r if r[k]!=plan['modules'][m].get(k)}=={'sha256'}
  changed.append(m)
assert set(changed)==set(pins['changes'])
actual=json.loads((BASE/'three-followon-attempt-37731710313-independent.json').read_text())
passed=set(actual['successful_module_names'])
assert len(passed)==177
for r in actual['source_checks']:
 if r['module'] in passed: assert plan['modules'][r['module']]['sha256']==r['sha256']
assert plan['topological_order']==[r['module'] for r in actual['source_checks']] or set(plan['topological_order'])=={r['module'] for r in actual['source_checks']}
assert len(plan['modules'])==179 and len(plan['targets'])==45 and plan['named_total']==501
assert sum(plan['named_counts'].values())==501 and plan['namespace_counts']=={'G6':352,'G3':134,'G5':15}
api=json.loads(git(COMMIT,PREP+'/API-INPUTS.json'))
apis=[]
for r in api['interfaces']:
 if 'repository_path' in r:
  b=git(ACTUAL,r['repository_path']);p=r['repository_path']
 else:
  p=r['local_source_path'];b=Path(p).read_bytes()
 assert sha(b)==r['sha256'],p
 apis.append({'path':p,'bytes':len(b),'sha256':sha(b)})
out={'schema':'actual177-two-followon-proof-only-source-selection-review-v1','candidate_commit':COMMIT,'actual_input':ACTUAL,'canonical_actual177_commit':'48d318b09136550347c43196f8e90d46ca2cef11','artifacts':artifacts,'changes':changes,'api_inputs':apis,'plan':record(COMMIT,planpath),'fixed_selection_fields':fixed,'requested_custom':179,'requested_named':501,'requested_namespace':plan['namespace_counts'],'changed_module_hashes':changed,'all177_actual_successful_hashes_fixed':True,'other177_requested_hashes_fixed':True,'all_imports_paths_targets_order_external_context_fixed':True,'successful_sum_rfl_unchanged':True,'planning_seconds':867,'job_cap_seconds':900,'per_command_cap_seconds':180,'compiler_invocations':0,'status':'SOURCE/API and exact STATIC selection ACCEPT; compiler UNCHECKED; no launch from this review'}
(BASE/'actual177-two-followon-repair-authentication.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'artifacts':len(artifacts),'changed_hashes':changed,'accepted_fixed':len(passed),'requested':[179,501],'planning_seconds':867}))
