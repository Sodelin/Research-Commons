#!/usr/bin/env python3
"""Independent source/bytes/Fraction QC only; never import or invoke targets.
Contributor: /root/solver_design_recovery. Creates only one attributed receipt
beside this reader in an existing counted WF. Fixed <=32KiB total allocation.
"""
import ast, copy, datetime, difflib, hashlib, json, os, re, resource, stat
from fractions import Fraction as F
from pathlib import Path

resource.setrlimit(resource.RLIMIT_AS, (256*1024**2, 256*1024**2))
W=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
G=W/'metadata/source-only-observer-execution-guard-20261011T0338Z'
H=W/'metadata/erased-selected-observer-validation-sourceonly-20261011T0327Z'
Q=Path(__file__).parent
OUT=Q/'FROZEN-OBSERVER-HARNESS-GUARD-SOURCE-QC.json'
CAP=32768
EXPECTED={
 G/'guard_erased_selected_observer_v1.py':(27217,'e7416c8012edf64a4f84cf24c98bc79d22d070cf8f71008f9a080462edf3e723'),
 G/'EXECUTION-CONFIG-V1.json':(24061,'a04d75654f8e5126eb99ac082c79643e60c12621614e2e15e6a1448c2947a227'),
 G/'SOURCE-FREEZE-V1.json':(7574,'2124dcbd8bb82804c19789c207702b9fe011c60d8edd9755b41ad8b3a0f2a833'),
 G/'GUARD-EXACT-DERIVATION.diff':(18365,'d769b8a5947b17f0e2fa93cc7ba15a7e1eeb446063d466dafe6b4785dcf233e0'),
 G/'PREPARED-GLOBAL-CAPACITY-V1.json':(4987,'bee66e251602cd507401b95631d7479b2aefd7b4a164dd0250e30fb630d98006'),
 G/'ROOT-CHECKPOINT-SOURCE-DESCRIPTOR.json':(983,'6b170012b773c6ab007bb3f01d2cb0aa19538adbe5da099cce16ce3f2fa15a96'),
 H/'erased_selected_observer_tests.rs':(13115,'8cd6034934823202fce96322a0a95781ef185ecae8de6a045a808af4c5506a21'),
 H/'PLAN.json':(8153,'862eec74e67825c06b7c682a519f44c4ec3c40c40a3c1536bfb649be86e7aa1e'),
 H/'SOURCE-FREEZE-2.json':(2246,'c76ea415605efa966d02a04275afca5419844f18cf28f3d177145b8bd0fc9019'),
}
def sha(b): return hashlib.sha256(b).hexdigest()
def canon(x): return sha(json.dumps(x,sort_keys=True,separators=(',',':')).encode())
def row(path):
 p=Path(path); h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''): h.update(b)
 return {'path':str(p),'bytes':p.stat().st_size,'sha256':h.hexdigest()}
checked={}
def pin(r):
 if isinstance(r,list): r={'path':r[0],'bytes':r[1],'sha256':r[2]}
 assert set(r)=={'path','bytes','sha256'},r
 got=row(r['path']); assert got==r,('pin',r,got)
 checked[r['path']]=got
 return got
def jp(path): return json.loads(Path(path).read_bytes())
def funcs(t): return {n.name:n for n in t.body if isinstance(n,ast.FunctionDef)}
def dump(t): return ast.dump(t,include_attributes=False)
def mapped(t,replacements):
 t=copy.deepcopy(t)
 for n in ast.walk(t):
  if isinstance(n,ast.Constant) and isinstance(n.value,str) and n.value in replacements: n.value=replacements[n.value]
 return dump(t)
def allocation(roots):
 # Independently includes directory-symlink inodes as well as directory/file
 # blocks. Never follows directory symlinks; regular-file targets deduplicated.
 s=set(); fs=set(); a=b=dirlinks=entries=0; rows=[]
 for root in roots:
  assert Path(root).is_dir(),root
  before=(a,b)
  for d,dirs,files in os.walk(root,followlinks=False):
   paths=[Path(d)]+[Path(d)/f for f in files]+[Path(d)/n for n in dirs if (Path(d)/n).is_symlink()]
   for p in paths:
    st=p.lstat(); entries+=1; key=st.st_dev,st.st_ino
    if key not in s: s.add(key); a+=st.st_blocks*512
    observed=[st]
    if stat.S_ISLNK(st.st_mode):
     target=p.stat()
     if stat.S_ISREG(target.st_mode): observed.append(target)
     elif stat.S_ISDIR(target.st_mode): dirlinks+=st.st_blocks*512
    for target in observed:
     key=target.st_dev,target.st_ino
     if key not in fs: fs.add(key); b+=target.st_blocks*512
  rows.append([root,a-before[0],b-before[1]])
 return {'lstat':a,'lstat_plus_regular_file_targets':b,'conservative':max(a,b),'directory_symlink_blocks':dirlinks,'entries':entries,'per_root':rows}
def own_allocation():
 return sum(p.lstat().st_blocks*512 for p in [Q,*Q.iterdir()])

for p,(n,h) in EXPECTED.items(): pin({'path':str(p),'bytes':n,'sha256':h})
cfg=jp(G/'EXECUTION-CONFIG-V1.json'); plan=jp(H/'PLAN.json'); freeze=jp(G/'SOURCE-FREEZE-V1.json')
for r in freeze['files']: pin(r)
for r in cfg['input_pins']: pin(r)
assert len(cfg['input_pins'])==len({r['path'] for r in cfg['input_pins']})==64
for key in ('helper_pin','plan_pin','current_producer_plan_pin','protected_result_pin','checkpoint_descriptor_pin','prior_guard_pin','prior_config_pin','harness_pin','observer_pin'):
 pin(cfg[key]); assert cfg[key] in cfg['input_pins']
prior=jp(cfg['protected_result_pin']['path']); old_cfg=jp(cfg['prior_config_pin']['path'])
old43=prior['final_authenticated_input_pins']
assert len(old43)==43 and canon(old43)=='651abd23a8b57f1f91c0ccca54e231e8840e3fab8da7ee073b697d9e2f7adf53'
assert cfg['input_pins'][:43]==old43==old_cfg['input_pins']
assert prior['status']=='PASS_FIVE_TARGETED_TESTS'
assert prior['private_binary']==cfg['original_private_ELF_bound_without_copy'] and prior['private_binary'] in cfg['input_pins']
assert prior['private_binary']['sha256']=='aaa7a2d2a87b9d2ba44afd34bf4a88aea2a1c9b45e069ffc0725250d4724a63e'
assert old43[33]['sha256']=='443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00'
for label,path,n,h in plan['new_inputs']:
 assert {'path':path,'bytes':n,'sha256':h} in cfg['input_pins'],label
observer_freeze=jp(plan['new_inputs'][1][1])
for r in observer_freeze['immutable_inputs']+observer_freeze['source_files']: pin(r)
assert observer_freeze['compile_native_test_or_target_import_authorized_or_performed'] is False
assert observer_freeze['all_semantic_provenance_independence_timed_native_flags_false'] is True
assert 'arbitrary literal Code Old unsupported' in observer_freeze['typed_Old_scope']
hfreeze=jp(H/'SOURCE-FREEZE-2.json')
for r in hfreeze['files']: pin(r)
assert not any(hfreeze['execution'].values()) and not any(hfreeze['scope_flags'].values())

producer=jp(cfg['current_producer_plan_pin']['path']); roots=producer['allocation_roots']
assert cfg['current_producer_plan_pin']['sha256']=='2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c'
assert roots==cfg['allocation_roots'] and len(roots)==len(set(roots))==26 and str(W) in roots
assert set(jp(old43[11]['path'])['allocation_roots']).issubset(roots)
limits={'scratch_hard_bytes':2147483648,'scratch_abort_bytes':2013265920,'memory_hard_bytes':17179869184,'memory_abort_bytes':16106127360,'fresh_output_reserve_bytes':50331648,'log_cap_per_stream_bytes':1048576,'compile_address_space_bytes':2147483648,'runtime_address_space_bytes':536870912,'compile_wall_seconds':120,'runtime_wall_seconds':120}
for k,v in limits.items(): assert cfg[k]==v,(k,cfg[k],v)
assert (producer['scratch_hard_limit_bytes'],producer['scratch_abort_bytes'],producer['memory_abort_bytes'])==(2147483648,2013265920,16106127360)
assert plan['resources']=={'compile_AS':2147483648,'compile_wall_s':120,'fresh_reserve':50331648,'logcap_each':1048576,'memory_hard':17179869184,'nonreclaimable_abort':16106127360,'poll_s':0.5,'proposed_filecap':16777216,'scratch_abort':2013265920,'scratch_hard':2147483648,'test_AS':536870912,'test_wall_s':120}
descriptor=jp(cfg['checkpoint_descriptor_pin']['path'])
assert descriptor['checkpoint']=='4862b9618ca422da4ad5381b5dec0a3fcac56e76'
assert descriptor['tree']=='145eefb4baaec4eafca16622ed9fdfb538313922'
assert descriptor['status']=='ROOT_SUPPLIED_SOURCE_DESCRIPTOR_ONLY' and descriptor['reused_rlibs_or_native_rebuilt_at_checkpoint'] is False

old=Path(cfg['prior_guard_pin']['path']).read_text(); new=Path(cfg['helper_pin']['path']).read_text()
old_ast=ast.parse(old); new_ast=ast.parse(new); a=funcs(old_ast); b=funcs(new_ast)
added=sorted(set(b)-set(a)); removed=sorted(set(a)-set(b)); changed=sorted(n for n in a if dump(a[n])!=dump(b[n]))
assert added==['allocation_details'] and not removed
assert changed==sorted(['allocated','measurements','limit_reason','authenticate_all','run_step','load_config','main'])
assert dump(a['run_step'])==mapped(b['run_step'],{'private_erased_selected_observer_guarded_step_v1':'private_selected_prefix_guarded_step_v1'})
assert dump(a['limit_reason'])==mapped(b['limit_reason'],{'FRESH_OUTPUT48MIB_LIMIT':'FRESH_OUTPUT32MIB_LIMIT'})
unchanged=sorted(n for n in a if dump(a[n])==dump(b[n]))
for n in ('proc_rows','remember_descendants','alive','signal_known','become_subreaper','stop_and_reap','child_caps','active_markers','memory','digest','authenticate','save_new','stamp'): assert n in unchanged
diff=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=cfg['prior_guard_pin']['path'],tofile=cfg['helper_pin']['path']))
assert diff==(G/'GUARD-EXACT-DERIVATION.diff').read_text()
# Read/AST predicates supplement full manual review, without executing functions.
for literal in ('ORIGINAL43_OMITTED_OR_CHANGED','CURRENT26_ROOT_LIST','NO_FALSE_REBUILD_ATTRIBUTION','EXACT_COMMAND_DRIFT','PRELAUNCH48MIB_RESERVE_NOT_AVAILABLE','FIVE_TEST_COUNT_NOT_OBSERVED','FIVE_TEST_SUCCESS_NOT_OBSERVED','POST_STEP_PIN_DRIFT','DESCENDANT_CLEANUP_INCOMPLETE','PIPE_DRAIN_TIMEOUT','GUARD_OR_EXECUTION_EXCEPTION','CREATE_NEW_OUTPUT_REQUIRED'):
 assert literal in new,literal
assert "os.O_CREAT|os.O_EXCL|os.O_WRONLY" in new and 'start_new_session=True' in new
assert "[authenticate(cfg['_configuration_pin'])]" in new
assert "observed_bytes_are_lower_bound_if_truncated" in new
assert "if keep<len(chunk):row['truncated']=True;reason=reason or kind.upper()+'_LOG_CAP'" in new
assert 'while child.poll() is None or selector.get_map():' in new
assert "'status':'PASS_PROCESS_EXIT_ZERO' if rc==0 and reason is None" in new

compile_args=cfg['compile_argv']; run_args=cfg['runtime_argv']; out=Path(cfg['output_directory'])
assert compile_args==plan['compile_argv'] and run_args==plan['runtime_argv']
assert compile_args[:4]==[old43[12]['path'],'--edition=2024','--test',cfg['harness_pin']['path']]
assert compile_args[-2:]==['-o',str(out/'erased-selected-observer-tests')]
assert run_args==[compile_args[-1],'--test-threads=1','--nocapture']
assert '-C' in compile_args and 'linker=/usr/bin/cc' in compile_args
externs=[compile_args[i+1] for i,x in enumerate(compile_args) if x=='--extern']
assert externs==[name+'='+old43[13+i]['path'] for i,name in enumerate(('parity_solver','calendar_cli','num_bigint','num_integer','num_traits'))]
assert len(externs)==5 and 'cargo' not in Path(compile_args[0]).name
tools=[]
for alias in ('/usr/bin/cc','/usr/bin/ld','/usr/bin/as'):
 resolved=str(Path(alias).resolve()); matches=[r for r in cfg['input_pins'] if r['path']==resolved]
 assert len(matches)==1,alias
 tools.append([alias,matches[0]])
assert cfg['environment']==plan['environment']
assert cfg['environment']['CARGO_INCREMENTAL']=='0' and cfg['environment']['PYTHONDONTWRITEBYTECODE']=='1'
assert all(cfg['environment'][k]==str(out/'tmp') for k in ('TMPDIR','TMP','TEMP'))
assert out==H/'execution-1' and str(out)==plan['working_directory'] and not out.exists()
assert cfg['all_outer_launch_captures_must_be_under']==str(G)

test_source=Path(cfg['harness_pin']['path']).read_text(); observer=Path(cfg['observer_pin']['path']).read_text()
test_names=re.findall(r'#\[test\]\s*fn\s+(\w+)\s*\(',test_source)
assert test_names==cfg['expected_test_names']==[r['name'] for r in plan['cases']] and len(test_names)==5
recorder=Path(old43[0]['path']).read_text()
assert '#[test]' not in recorder and '#[test]' not in observer
for p in (old43[0]['path'],cfg['observer_pin']['path']): assert '#[path="'+p+'"]' in test_source
for token in ('9_007_199_254_740_993','end:prefix::End::After(13)','let a=observe(&t,11)','v.register[3]=false','reg[3]=false','old[5].population','order.swap(0,1)','assert_eq!(actual_fibres(&a),flat_two_copy_fibres(&t,11))','spec.limits.nodes-=1','child.provider_limits.boundary.assignments=0'):
 assert token in test_source,token
for token in ('*bit = false','(parent,state)','let key = (old_leaf,format!','self.arithmetic.sum_into(Stage::JointFibres','mass != Polynomial::one','spec.old_prefix_len > entry','input.work().initializer_calls != 1','population::unordered_forest','pub fn literal_code_old_supported(&self) -> bool { false }'):
 assert token in observer,token
assert 'word::word_row(' not in observer and 'Initial::Natural' not in observer
assert 'Initializer' not in observer
# Explicit finite hand formula, independent of all target evaluators. Variables
# are abstract names; no target law/reader/initializer is called by this reader.
def padd(p,q):
 r=p.copy()
 for k,v in q.items():
  r[k]=r.get(k,F(0))+v
  if not r[k]: del r[k]
 return r
def pmul(p,q):
 r={}
 for k,v in p.items():
  for j,w in q.items(): r=padd(r,{tuple(sorted(k+j)):v*w})
 return r
def var(x): return {(x,):F(1)}
one={():F(1)}; g0=var('G0'); g1=var('G1')
ng0=padd(one,{k:-v for k,v in g0.items()}); ng1=padd(one,{k:-v for k,v in g1.items()})
upper=padd(pmul(ng0,var('X3E2')),pmul(g0,var('X3E3')))
base=pmul(pmul(var('X0E7'),var('X2E4')),upper)
expected=[pmul(pmul(ng1,var('X1E5')),base),pmul(pmul(g1,var('X1E6')),base)]
assert len(expected[0])==6 and len(expected[1])==3
def evaluate(p,values):
 total=F(0)
 for k,v in p.items():
  for name in k: v*=values[name]
  total+=v
 return total
values={x:F(1,2) for x in ('X0E7','X1E5','X1E6','X2E4','X3E2','X3E3')}; values.update(G0=F(1,3),G1=F(2,5))
numerical=[evaluate(p,values) for p in expected]
assert numerical==[F(3,80),F(1,40)] and sum(numerical)==F(1,16)
assert padd(ng0,g0)==one

markers=[str(Path(r)/'ACTIVE-GUARDED-PROCESS.json') for r in roots if (Path(r)/'ACTIVE-GUARDED-PROCESS.json').exists()]
assert not markers and not out.exists()
assert own_allocation()<=24576
usage=allocation(roots)
usage['per_root_canonical_sha256']=canon(usage.pop('per_root'))
memstat=dict(x.split() for x in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())
mem={k:int(memstat[k]) for k in ('anon','shmem','kernel')}; mem['nonreclaimable']=sum(mem.values())
# Account full remaining own artifact allocation before creating receipt. Root
# must rerun its exact exclusive prelaunch measurement; this is a dated reading.
remaining=CAP-own_allocation()
assert usage['conservative']+remaining+50331648<2013265920
assert mem['nonreclaimable']<16106127360
stat_rows=[[r['path'],r['bytes'],r['sha256'],Path(r['path']).stat().st_dev,Path(r['path']).stat().st_ino,Path(r['path']).stat().st_size] for r in cfg['input_pins']]
report={
 'schema':'independent_erased_selected_observer_harness_guard_source_qc_v1',
 'status':'PASS_SOURCE_HARNESS_FORMULA_AND_FIXED_GUARD_REMEASURED_CAPACITY_ONLY',
 'reviewer':'/root/solver_design_recovery', 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'helper_sha256':cfg['helper_pin']['sha256'],'config_sha256':EXPECTED[G/'EXECUTION-CONFIG-V1.json'][1],
 'source_freeze_sha256':EXPECTED[G/'SOURCE-FREEZE-V1.json'][1],
 'plan_sha256':cfg['plan_pin']['sha256'],'harness_sha256':cfg['harness_pin']['sha256'],'observer_sha256':cfg['observer_pin']['sha256'],
 'reader':row(__file__),
 'identity_checks':{'config_input_pins':64,'original43_prefix_exact':True,'configuration_is_dynamic65th_guard_pin':True,'all_authentications_unique_paths':len(checked),'all_rows_canonical_sha256':canon(sorted(checked.values(),key=lambda r:r['path'])),'config_array_sha256':canon(cfg['input_pins']),'input_stat_rows_sha256':canon(stat_rows),'roots_count':26,'ordered_roots_sha256':canon(roots),'full_freezes_and_exact_derivation_checked':True,'observer_full42_input_and_source_rows_checked':True,'protected_public':old43[33],'protected_prior_private':prior['private_binary']},
 'derivation':{'added_functions':added,'changed_functions':changed,'unchanged_functions':unchanged,'run_step_only_schema_literal':True,'limit_reason_only48MiB_label':True,'cleanup_subreaper_PID_birth_group_reap_and_child_caps_AST_identical':True,'all_other_changes_manually_read_full_source':True},
 'protocol':['Only authenticated direct rustc --test with five exact old rlibs and resolved cc/ld/as; fixed child/output/tmp argv, no Cargo rebuild/fallback/retry. All64 plus configuration rehashed pre/post; generated private binary hashed before and after tests.', 'Exact frozen26 allocation roots. Conservative independent inode accounting includes directory blocks/symlink inodes and regular-file targets; no directory-symlink recursion. Fresh counter covers guard preparation/captures plus execution/tmp; serial WF marker also counts globally.', 'Linux subreaper before child; child new session/group, PID-birth tracking and proc-tree/adopted descendants; stop/kill/wait/reap in normal and exception paths. Surviving descendants, timeout, incomplete pipe draining or truncation refuse PASS. Nonadversarial Linux contract only.', 'Per-child AS2GiB/512MiB and wall120s, CPU125s, FSIZE16MiB/core0; each stream/sample1MiB. PASS requires zero exit, no reason, EOF selector drained, untruncated capture, stable pins and exact five named test summary. Exceptional capture is preserved failure, not complete PASS evidence.', 'External root/sole-scheduler exclusive approval is mandatory; --execute-approved is acknowledgement only. Outer launcher captures must be under fixed G to be counted. No process or target helper was imported or invoked by QC.'],
 'five_test_heads':test_names,
 'manual_harness_review':['Empty natural initializer: four latent seeds project to two G1/(1-G1) fibres, all seven register slots retained with only vertex3 resetfalse; immutable input and initializer1/query0 asserted.', 'Full exact symbolic unmerged mass retains lower bit5 in every Old endpoint and Edge5/6 at endpoint5. Gamma is original1/3,2/5, not old parent-zero2/3,3/5. Old cut11 lies before Enter3; final13 includes upper interval3. This is a native fixture, not typed support/source admission.', 'Flat oracle walks every recorder row/whole Old vector, clones and clears only slot3, uses explicit two-copy forests with global BIG/0, sums every joint fibre. It does not invoke observer interners/forest helper. Equal final forest/different Old stays distinct; latent erased-only fibres sum.', 'Three carried components keep global labels0,17,9007199254740993. Supplied literal tied Enter swap preserves final but changes intermediate Old; no typed compiler-order claim.', 'Exact-node/one-below, zero input/bit/addition caps, invalid hybrid/Old/nonCOMMON and recorder-child UNKNOWN are explicit refusals; Unknown contains no partial Table. Existing all-source semantics remain unverified.'],
 'independent_small_hand_formula':{'expression':'w_b X(0,7) X(1,5+b) X(2,4) [(1-G0) X(3,2)+G0 X(3,3)]','w0':'1-G1','w1':'G1','expanded_exact_terms':[len(p) for p in expected],'expanded_polynomial_canonical_sha256':canon([[[list(k),str(v)] for k,v in sorted(p.items())] for p in expected]),'all_X_half_original_G0_third_G1_two_fifths':[str(v) for v in numerical],'sum':'1/16','empty_erased_G0_marginal_identity':True,'not_a_target_evaluation_or_runtime_result':True},
 'limits':limits,'frozen_descriptor':descriptor,
 'capacity_dated':{'fresh_reader_measurement':usage,'memory':mem,'full48MiB_projected_including_remaining_Q_allowance':usage['conservative']+remaining+50331648,'abort_margin_after_projection':2013265920-usage['conservative']-remaining-50331648,'remaining_Q_allowance_in_projection':remaining,'markers':markers,'output_absent':True,'mandatory_root_prelaunch_remeasurement':True,'sampled_peak_or_future_guarantee':False},
 'allocation':{'cap_including_directory_bytes':CAP,'current_source_and_directory_blocks':own_allocation(),'serialized_report_limit_bytes':8192,'directory_blocks_counted':True,'remaining_included_in_global_projection':True},
 'scope':'Fixed private observer/harness/guard readiness only. Whole erased Selected Old and full carried unranked forest/outside register; arbitrary literal Code Old is unsupported. Only named hybrid original vertex3 is resetfalse in output; latent bank/conditional transitions and every other register slot unchanged. No runtime PASS, Lean/native refinement, typed encoding/order/no-read/support/independence, new G6 factorization/source admission/timed/public promotion or combined1575 kernel acceptance. Local4862/tree145e is a root-supplied source descriptor, not rebuilt rlib provenance.',
 'target_import_compile_native_reference_Git_or_overlay_operations':False,
 'external_exclusive_root_gate_still_required':True,
}
raw=(json.dumps(report,sort_keys=True,separators=(',',':'))+'\n').encode()
assert len(raw)<=8192,('receipt_size',len(raw))
assert own_allocation()+((len(raw)+4095)//4096)*4096<=CAP
with OUT.open('xb') as f: f.write(raw)
assert own_allocation()<=CAP
print(json.dumps({'status':report['status'],'receipt':row(OUT),'reader':row(__file__),'own_allocated_bytes_including_directory':own_allocation(),'capacity_conservative':usage['conservative'],'projected48MiB_plus_remainingQC':report['capacity_dated']['full48MiB_projected_including_remaining_Q_allowance'],'nonreclaimable':mem['nonreclaimable'],'markers':markers,'target_operations':False},sort_keys=True))
