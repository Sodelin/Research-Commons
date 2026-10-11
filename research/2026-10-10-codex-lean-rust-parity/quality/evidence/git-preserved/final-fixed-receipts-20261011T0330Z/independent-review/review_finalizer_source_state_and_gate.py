#!/usr/bin/env python3
"""Own bounded source/saved-state reader. No target imports or Git commands."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,ast,sys,traceback,os,zlib
W=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
SUP=W/'design-qc/exact-publication-recovery-v3-20261011T0302Z-solver_design_recovery/review_partial_and_recovery_v3.py'
raw=SUP.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='807dbe710f49944badb8c5c7d64a5d65709333651800bafc31e1c72a9e15cd67'
# Execute only our preserved stdlib byte readers, stopping before prior QC logic.
n={};exec(compile(raw.split(b'\ndef jp(',1)[0],str(SUP),'exec'),n)
for k in ['P','B','INDEX','POOLS','pin','digest','require','obj','tree_path','commit_tree','index_entries','canonical_hash','free_bytes','allocation','encode_tree','object_present','stage_bytes','current_head']:globals()[k]=n[k]
Q=Path(__file__).parent
F='fdd10f63a2d9c27f84cc42144203569f7e81fc60dbb1f4f95067cce8d511491b'
CONFIG=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/RESOURCE-AND-RUN-PLAN.json')
CPIN='2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c'
BASE='c47535d42987f807b097125fb31966ee353b253c'
PIN={
'finalize_remaining_fixed_checkpoint_20261011.py':F,
'publish_exact_compressed_checkpoint_20261011.py':'c3479b7fcc3cc57e7485c7fdd6fa6fb4beef3b89c0a0ae046737ff879eeb6a24',
'recover_exact_compressed_checkpoint_v3_20261011.py':'d7bc29eafca8f53e4231f880c0d13061c79d7d69ba27c1ed1a886697f327ed7e',
'preserve_bounded_late_receipts_20261011.py':'a769096c38dc32a9567c939cf8f15283629b8b43ca9693e33c6d4b2672fd28a2',
'EXACT-COMPRESSED-CHECKPOINT-FUNDING-GATE.json':'b1a260456c2c09673e8d811235f5778bdcb57e530948e12b82163cee87c1cce4',
'EXACT-COMPRESSED-CHECKPOINT-PUBLICATION.json':'26df427af739b50f54aae717b4c1f58d5031437515481f8dca9ffebe9a1e9aae',
'EXACT-COMPRESSED-CHECKPOINT-PARTIAL-FAILURE-STATE.json':'11fec1822e2abdafb3b776547171205b8ffaf179fce7fa1f462576808fa70595',
'BOUNDED-LATE-RECEIPTS-INPUTS.json':'ab8f9c972455eaee9973332cc834068a89d250b35afcf13594da4589984af1e9',
'BOUNDED-LATE-RECEIPTS-PUBLICATION.json':'7fb9beb9fd367df5117e6ef98b50291b403c0264e1fa14fd5bc745a6feebd33a',
'LATE-FINAL-RECEIPT-TREE-SUBRESERVE-FAILURE-STATE.json':'4758507fd71a96cbe7d3ccb4fe0b26de48749d058e200ec78f47976f2c0e0b21'}
def load(p,h=None):
 i,d=pin(p,h);return i,json.loads(d)
def blob(data):
 full=b'blob '+str(len(data)).encode()+b'\0'+data
 return hashlib.sha1(full).hexdigest(),len(zlib.compress(full,6))
def entries_tree(e):return encode_tree({p:(format(v['mode'],'o'),v['git_blob']) for p,v in e.items()})
def source():
 data=(B/'finalize_remaining_fixed_checkpoint_20261011.py').read_bytes();require(digest(data)==F and len(data)==8286,'exact finalizer source')
 a=ast.parse(data);f={x.name:x for x in a.body if isinstance(x,ast.FunctionDef)}
 require(set(f)=={'digest','row','inputs','costs','funding','prepare','apply'},'bounded function inventory')
 const={x.targets[0].id:ast.literal_eval(x.value) for x in a.body if isinstance(x,ast.Assign) and isinstance(x.targets[0],ast.Name) and x.targets[0].id in {'BASE_TREE','BASE_POOL','BLOB_LEFT','TREE_LEFT','COMMIT_LEFT','FUNDED_MAX'}}
 require(const=={'BASE_TREE':BASE,'BASE_POOL':99707172,'BLOB_LEFT':95096,'TREE_LEFT':91206,'COMMIT_LEFT':16384,'FUNDED_MAX':99909858},'exact remaining original constants')
 text=data.decode();tok={
'inputs':["m['publisher_sha256']==digest(pathlib.Path(__file__))","len({x['git_tree_path'] for x in rows})==len(rows)","tree==BASE_TREE","A.pool()==BASE_POOL","p not in entries and not (A.R/x['git_tree_path']).exists()"],
'costs':['A.missing(x[\'git_blob\'] for x in rows)','A.missing(ts)',"sum(x['zlib6_content_bytes'] for x in unique.values())"],
'funding':['blobs<=BLOB_LEFT and trees<=TREE_LEFT',"resource['pool_bytes']+blobs+trees+COMMIT_LEFT<=FUNDED_MAX<A.POOL_LIMIT","allocation<=original['new_loose_files_dirs_and_late_alloc_funding_bytes']",'+allocation<2013265920'],
'apply':["review['finalizer_source_sha256']==digest(pathlib.Path(__file__))","gate['manifest_sha256']==digest(M)","gate['base_index_entries_sha256']==A.sha(raw)","costs(rows+[rx],entries)","Q.write_blob_preserving_existing(x)","not in added)==raw","A.git('show',':'+x['git_tree_path'])==pathlib.Path(x['source_path']).read_bytes()","with OUT.open('xb')","actual==entries","A.git('show',':'+rx['git_tree_path'])==receipt_bytes","after['pool_bytes']<=BASE_POOL+blobs+trees"]}
 for name,ts in tok.items():
  part=ast.get_source_segment(text,f[name])
  for t in ts:require(t in part,'protocol predicate '+name+':'+t)
 calls=[x for x in ast.walk(a) if isinstance(x,ast.Call) and isinstance(x.func,ast.Attribute) and isinstance(x.func.value,ast.Name) and x.func.value.id=='A' and x.func.attr=='git']
 kinds=[ast.literal_eval(x.args[0]) for x in calls]
 require(set(kinds)=={'rev-parse','update-index','show','ls-files','write-tree'} and kinds.count('write-tree')==1,'only fixed index reads/additions and one final tree write')
 part=ast.get_source_segment(text,f['apply'])
 order=[part.index(x) for x in ['costs(rows+[rx],entries)','funding(resource,blobs,trees,allocation+256*1024)','for x in rows:Q.write_blob_preserving_existing(x)','stage(rows)','not in added)==raw',"with OUT.open('xb')",'Q.write_blob_preserving_existing(rx)',"A.git('write-tree')"]]
 require(order==sorted(order),'exact complete receipt funding before Git writes and receipt only after full original row readback')
 require(all(x not in text for x in ['unlink','rmtree','fetch','os.replace','commit-tree','update-ref']),'no deletion/fetch/scope/HEAD/ref changes')
 return {'source_sha256':F,'source_bytes':len(data),'constants':const,'exact_receipt_in_pre_mutation_funding':True,'full_input_readback_before_create_new_receipt':True,'one_final_write_tree_call':True,'ordered_fixed_git_command_kinds':sorted(set(kinds)),'current_original_pool_and_all_remaining_budgets_locked':True,'no_recursive_self_hash_or_self_tree':True,'trusted_manifest_scope':'Root must freeze all UTF8 rows, new absent normalized prefix paths, source/hash/size and gate before apply; this is not arbitrary manifest admission. Reserved gate/receipt destinations must be absent and excluded from listed rows.','prelaunch':'Exact finalizer/V3/A/late sources and M/G/review bytes must be rehashed with PYTHONDONTWRITEBYTECODE=1; independent final frozen-M/G readback still required.'}
def saved_state():
 pins=[pin(B/name,h)[0] for name,h in PIN.items()]
 _,g=load(B/'EXACT-COMPRESSED-CHECKPOINT-FUNDING-GATE.json',PIN['EXACT-COMPRESSED-CHECKPOINT-FUNDING-GATE.json'])
 _,late=load(B/'BOUNDED-LATE-RECEIPTS-PUBLICATION.json',PIN['BOUNDED-LATE-RECEIPTS-PUBLICATION.json'])
 _,m=load(B/'BOUNDED-LATE-RECEIPTS-INPUTS.json',PIN['BOUNDED-LATE-RECEIPTS-INPUTS.json'])
 _,hold=load(B/'LATE-FINAL-RECEIPT-TREE-SUBRESERVE-FAILURE-STATE.json',PIN['LATE-FINAL-RECEIPT-TREE-SUBRESERVE-FAILURE-STATE.json'])
 e,info=index_entries(INDEX.read_bytes());require(current_head()=='2347f1c16bfaf649da33ef0a42d693b97f46a161','HEAD retained')
 rows=m['files']+[{'source_path':str(B/'BOUNDED-LATE-RECEIPTS-INPUTS.json'),'git_tree_path':m['prefix']+'/LATE-INPUT-MANIFEST.json','bytes':18013,'sha256':PIN['BOUNDED-LATE-RECEIPTS-INPUTS.json']}]
 bindings=[]
 for r in rows:
  _,data=pin(r['source_path'],r['sha256'],r['bytes']);data.decode('utf8');v=e[r['git_tree_path']]
  require(v['mode']==0o100644 and v['stage']==0 and v['skip_worktree'],'regular late index entry')
  require(obj(v['git_blob'])==('blob',data),'complete late original/raw blob equality')
  bindings.append([r['git_tree_path'],v['git_blob'],len(data),digest(data)])
 actual,_=entries_tree(e);require(actual==BASE==late['tree_without_this_receipt']==hold['current_tree'],'current saved late tree')
 added={r['git_tree_path'] for r in rows};previous,_=entries_tree({p:v for p,v in e.items() if p not in added})
 require(previous=='451a3ed51fd20f553a8807e859d5176a6ad6ecfc','all prior mode/OID entries unchanged below exact late30')
 require(m['prefix']+'/BOUNDED-LATE-RECEIPTS-PUBLICATION.json' not in e,'held receipt not already indexed')
 original=g['resource']['pool_bytes']+g['complete_object_content_funding_bytes']
 remain_blob=g['late_blob_reserve_bytes']-late['exact_new_blob_content_bytes'];remain_tree=g['late_tree_reserve_bytes']-late['exact_new_tree_content_bytes']
 pool=sum(p.stat().st_size for p in POOLS[0].rglob('*') if p.is_file())
 require(pool==99707172 and remain_blob==95096 and remain_tree==91206,'exact actual remaining budgets')
 require(pool+remain_blob+remain_tree+g['commit_reserve_bytes']==original==99909858<100663296,'unchanged fixed funding envelope')
 return {'pinned_current_and_retained_failure_bytes_canonical_sha256':canonical_hash(pins),'pinned_names_and_hashes':PIN,'late30_count':len(rows),'late30_full_raw_bytes':sum(r['bytes'] for r in rows),'late30_bindings_canonical_sha256':canonical_hash(bindings),'current_index':info,'stage_mode_oid_path_sha256':digest(stage_bytes(e)),'HEAD':'2347f1c16bfaf649da33ef0a42d693b97f46a161','current_tree':actual,'prior_tree_without_only30_late_paths':previous,'previous_all_mode_and_OID_entries_retained':True,'original_receipt_present_full_local_but_not_indexed':True,'failed_tree_slice':{'need':37327,'slice':32768,'fits_remaining_original_tree_budget':True},'remaining_blob_bytes':remain_blob,'remaining_tree_bytes':remain_tree,'remaining_commit_bytes':g['commit_reserve_bytes'],'actual_pool_bytes':pool,'fixed_funded_max_pool_bytes':original,'fixed_pool_cap_bytes':100663296,'previous_proof_audits_not_repeated':True},e

def resources():
 _,cfg=load(CONFIG,CPIN);roots=cfg['allocation_roots'];require(len(roots)==26 and len(set(roots))==26 and all(Path(p).is_dir() for p in roots),'exact26 existing ordered roots')
 pin('/dev/shm/rc-source-fit-native-20261010T221453.635194Z/target/debug/source-fit-solver','443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00')
 ls=allocation(roots);fs=allocation(roots,True);non={k:int(v) for k,v in (line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())}
 nr=non['anon']+non['shmem']+non['kernel'];ownreserve=32768;future=2797568
 require(max(ls['distinct_allocated_bytes'],fs['distinct_allocated_bytes'])+future+ownreserve<2013265920,'current global plus entire original allocation and bounded own QA reserves')
 require(nr<16106127360 and free_bytes('/tmp')>=INDEX.stat().st_size+2097152 and free_bytes('/workspace')>=8388608,'fixed memory/tmpindex/overlay floors')
 return {'config_sha256':CPIN,'ordered26_roots_canonical_sha256':canonical_hash(roots),'lstat_file_and_directory_allocated_bytes':ls['distinct_allocated_bytes'],'followed_file_target_and_directory_allocated_bytes':fs['distinct_allocated_bytes'],'entire_original_loose_file_fanout_late_allocation_reserve':future,'own_Q_directory_budget_bytes':ownreserve,'scratch_abort_bytes':2013265920,'scratch_hard_bytes':2147483648,'nonreclaimable_bytes':nr,'nonreclaimable_abort_bytes':16106127360,'tmp_free_bytes':free_bytes('/tmp'),'index_plus2MiB_bytes':INDEX.stat().st_size+2097152,'overlay_free_bytes':free_bytes('/workspace'),'overlay_floor_bytes':8388608,'instantaneous_snapshot_not_universal_future_bound':True}

def frozen_gate(e):
 mi,m=load(B/'FINAL-REMAINING-FULLTEXT-INPUTS.json');gi,g=load(B/'FINAL-REMAINING-FIXED-RESERVE-GATE.json')
 require(m['publisher_sha256']==F and g['publisher_sha256']==F and g['manifest_sha256']==mi['sha256'],'full final manifest/gate source bindings')
 require(g['base_index_entries_sha256']==digest(stage_bytes(e)) and g['base_tree']==BASE and g['base_pool_bytes']==99707172,'frozen current index/tree/pool binding')
 require(g['original_funding_gate_sha256']==PIN['EXACT-COMPRESSED-CHECKPOINT-FUNDING-GATE.json'],'original funding retained')
 require([g[x] for x in ['remaining_blob_content_bytes','remaining_tree_content_bytes','commit_content_bytes','original_funded_max_pool_bytes']]==[95096,91206,16384,99909858],'no quota change')
 prefix=m['prefix'];require(prefix=='research/2026-10-10-codex-lean-rust-parity/quality/evidence/git-preserved/latest1570-handoff-20261011T0245Z','exact approved prefix')
 reserved={prefix+'/FINAL-FIXED-RESERVE-GATE.json',prefix+'/FINAL-REMAINING-FULLTEXT-PUBLICATION.json'}
 rows=m['files']+[{'source_path':mi['path'],'git_tree_path':prefix+'/FINAL-INPUT-MANIFEST.json','bytes':mi['bytes'],'sha256':mi['sha256']}]
 require(len({r['git_tree_path'] for r in rows})==len(rows),'unique final input paths')
 predicted={p:(format(v['mode'],'o'),v['git_blob']) for p,v in e.items()};bodypins=[];objects={}
 for r in rows:
  path=r['git_tree_path'];require(path.startswith(prefix+'/') and '..' not in Path(path).parts and path not in e and path not in reserved and not (n['REPO']/path).exists(),'new normalized absent final destination')
  _,d=pin(r['source_path'],r['sha256'],r['bytes']);d.decode('utf8');oid,size=blob(d);predicted[path]=('100644',oid);bodypins.append([path,oid,len(d),digest(d)])
  if not object_present(oid):objects[oid]=size
  else:require(obj(oid)==('blob',d),'already-held full original final bytes')
 require(all(p not in predicted and not (n['REPO']/p).exists() for p in reserved),'new reserved gate and actualreceipt paths')
 root,trees=encode_tree(predicted);tb=sum(x[2] for x in trees if not object_present(x[0]));bb=sum(objects.values())
 require(bb==g['known_rows_blob_bytes'] and tb==g['known_rows_tree_bytes'] and len(rows)==g['known_rows_count'],'independent exact knownrows funding and paths')
 require(bb<=95096 and tb<=91206,'knownrows fit original remaining reserves')
 # Actual future receipt and gate are additionally charged by immutable apply before any writes.
 return {'manifest':mi,'gate':gi,'all_frozen_rows_count_with_manifest':len(rows),'full_raw_bytes':sum(r['bytes'] for r in rows),'row_bindings_canonical_sha256':canonical_hash(bodypins),'known_rows_exact_missing_zlib6_blob_bytes':bb,'known_rows_exact_missing_tree_bytes':tb,'known_rows_pure_tree':root,'known_rows_expected_root_not_written_yet':True,'complete_gate_and_actual_receipt_costs_mandatory_pre_mutation_check':True,'no_arbitrary_reserved_destination_collisions':True,'fresh_finalizer_source_review_does_not_accept_any_new_math_or_runtime':True}

phase=sys.argv[1] if len(sys.argv)>1 else 'source'
out=Q/('FINALIZER-SOURCE-AND-LATE-SAVED-STATE-QC.json' if phase=='source' else 'FINALIZER-FROZEN-MANIFEST-GATE-QC.json')
require(not out.exists(),'new immutable own receipt')
result={'schema':'solver-design-recovery/final-fixed-publication-independent-qc-v1','contributor':'/root/solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_path':str(Path(__file__)),'reviewer_sha256':digest(Path(__file__).read_bytes()),'finalizer_source_sha256':F,'phase':phase,'status':'FAIL_OWN_READER','scope':'Fixed Git evidence byte preservation only. No Git commands/mutations, target imports, compiler/native/helper/evaluator, semantic admission or remote success claims.'}
try:
 result['source_protocol']=source();state,e=saved_state();result['saved_state']=state
 if phase=='gate':result['frozen_final_rows_and_gate']=frozen_gate(e)
 result['current_resources']=resources()
 result['own_exploratory_failure_and_correction']={'failure':'KeyError: guessed self-manifest destination prefix/BOUNDED-LATE-RECEIPTS-INPUTS.json in ephemeral standard-library reader.','correction':'Read frozen late helper text; its exact destination is prefix/LATE-INPUT-MANIFEST.json. Corrected ephemeral readback and this retained reader pass all30. No target source or producer changed.'}
 result['status']='PASS_FINALIZER_SOURCE_AND_SAVED_STATE_FINAL_FROZEN_GATE_STILL_REQUIRED' if phase=='source' else 'PASS_FINALIZER_FIXED_FROZEN_ROWS_GATE_AND_REMAINING_ORIGINAL_RESERVES'
 if phase=='gate':result['finalizer_gate_sha256']=result['frozen_final_rows_and_gate']['gate']['sha256']
except Exception as exc:
 result['error']=str(exc);result['traceback']=traceback.format_exc()
with out.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
allocated=sum(p.stat().st_blocks*512 for p in Q.iterdir() if p.is_file())+Q.stat().st_blocks*512
print(json.dumps({'status':result['status'],'path':str(out),'sha256':digest(out.read_bytes()),'bytes':out.stat().st_size,'finalizer_source_sha256':F,'directory_full_allocated_bytes':allocated,'error':result.get('error')}))
sys.exit(0 if result['status'].startswith('PASS') and allocated<=32768 else 1)
