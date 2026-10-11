"""Read-only standard1509 full-audit/storage feasibility observation.

Contributor: Codex / lean_integration_successor, 2026-10-11.
This never imports a builder, stages a context, launches a compiler or decodes
an audit. All new outputs are attributed metadata in the existing counted root.
Cache headers/existing objects are observations, never current-run admissions.
"""
from pathlib import Path
import datetime,hashlib,json,os

W=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
BASE=Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z')
L=Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/lean')
OUT=Path(__file__).parent
DELTA=Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z/metadata/integration-source-identity-delta-1509-20261011T015156.237141Z/INTEGRATION-SOURCE-IDENTITY-DELTA.json')
COMPILER='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
NATIVE='6f8ad181b1b3b832d74cf0f88255b519a3512252c343d3e0cde0c540cbfe7aac'
MIB=2**20

def sha(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  for b in iter(lambda:f.read(MIB),b''):h.update(b)
 return h.hexdigest()

def pin(path):
 p=Path(path);return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}

def save(path,data):
 with Path(path).open('x') as f:json.dump(data,f,indent=2);f.write('\n')

def measure(roots,follow=False):
 seen=set();total=0;per=[]
 for root in roots:
  subtotal=0
  for directory,_,files in os.walk(root):
   for p in [Path(directory),*(Path(directory)/n for n in files)]:
    s=p.stat() if follow else p.lstat();key=(s.st_dev,s.st_ino)
    if key not in seen:seen.add(key);subtotal+=s.st_blocks*512
  total+=subtotal;per.append({'root':root,'allocated_bytes_deduplicated_in_root_order':subtotal})
 return {'allocated_bytes':total,'distinct_inodes':len(seen),'per_root':per}

plan=json.loads((W/'RESOURCE-AND-RUN-PLAN.json').read_text())
delta=json.loads(DELTA.read_text());assert sha(DELTA)=='242535f8d6748df81b5c376d5c3aa1ebe44e2cd4594f8099e240e2f4505a5e6d'
assert delta['counts']['local_static_combined_identity_set']==1509 and delta['counts']['shared_source_import_conflicts']==0
base=json.loads((BASE/'DEPENDENCY-GRAPH.json').read_text())['targets']['current/connected']
expected={m:r['sha256'] for m,r in base['modules'].items()}
expected.update({r['module']:r['sha256'] for r in delta['genuinely_new_modules']})
assert len(expected)==1509
choices={n:BASE for n in base['modules']}
choices.update({'G7OriginalFamilyCalendarNormalization':Path('/dev/shm/rc-lean-g7-family-normalization-20261010T230143.534018Z'),'G6OriginalParallelArmTransport':Path('/dev/shm/rc-lean-g6-parallel-arm-transport-20261010T231844.690779Z'),'G6OriginalForestRegisterCompression':Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z'),'G6OriginalCommonPrefix':W,'G6NaturalCommonForestFactorization':W})
selected={}
for owner in set(choices.values()):
 for entry in (owner/'.build/cache').iterdir():
  if not entry.is_dir():continue
  rp=entry/'receipt.json';rec=json.loads(rp.read_text());n=rec['module']
  if choices.get(n)!=owner or rec['source_sha256']!=expected[n]:continue
  assert n not in selected
  assert rec['status']=='PASS_FRESH_KERNEL_CHECK' and rec['exit_code']==0
  assert rec['compiler_sha256']==COMPILER and rec['native_runtime_digest']==NATIVE
  assert rec['native_initialized_libraries_bound'] and rec['native_runtime_stat_stable']
  assert all(s in rec['command'] for s in ['-j1','-t0','-Ddebug.skipKernelTC=false'])
  obj=Path(rec['cached_object']);assert obj.is_file()
  selected[n]={'module':n,'source_sha256':rec['source_sha256'],'provider_workspace':str(owner),'cache_key':entry.name,'receipt':pin(rp),'cached_object':str(obj),'cached_object_bytes':obj.stat().st_size,'status':'EXISTING_COMPLETED_HEADER_AND_PATH_OBSERVED_NOT_FUTURE_ADMISSION'}
assert set(selected)==set(expected)
projection=OUT/'EXISTING-CACHE-HEADER-PROJECTION-1509.json'
save(projection,[selected[n] for n in sorted(selected)])

roots=plan['allocation_roots'];assert len(roots)==26
lstat,follow=measure(roots),measure(roots,True)
run=BASE/'.build/runs/20261010T223805.816906Z'
profile={};rows=[]
for directory,dirs,files in os.walk(run):
 if Path(directory).name=='objects':dirs[:]=[];continue
 for n in files:
  p=Path(directory)/n;s=p.stat();rel=str(p.relative_to(run))
  category='old_uncompressed_native_loader' if n.startswith('NATIVE-LOADER.') else 'raw_owned_audit' if n=='AUDIT-RESULT.json' else 'fresh_aggregate_olean' if n.endswith('.olean') else 'other_run_metadata'
  profile[category]=profile.get(category,0)+s.st_blocks*512
  if category=='other_run_metadata':rows.append({'path':str(p),'bytes':s.st_size,'allocated_bytes':s.st_blocks*512})
assert profile['raw_owned_audit']==114302976 and profile['other_run_metadata']==42766336
native_reserve=2*MIB
best_tested=profile['raw_owned_audit']+profile['other_run_metadata']+profile['fresh_aggregate_olean']+native_reserve
reserves={'full_raw_owned_audit_existing_codec128MiB_ceiling':128*MIB,'runtime_metadata44MiB_existing40_8MiB_profile':44*MIB,'preparation_source_graph_cache_transport_metadata20MiB':20*MIB,'two_complete_gzip_native_captures':2*MIB,'fresh_aggregate_object_and_source':MIB,'lossless_delta_and_other_gzip_export8MiB':8*MIB,'posttransport_inventory_saved_QA_and_transients4MiB':4*MIB}
reserve=sum(reserves.values());abort=plan['scratch_abort_bytes'];hard=plan['scratch_hard_limit_bytes']
pool=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/git-object-pool-preserved-20261011');pool_sizes=[]
for directory,_,files in os.walk(pool):
 for n in files:
  s=(Path(directory)/n).stat();pool_sizes.append((s.st_size,s.st_blocks*512))
memory_stat=dict(line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines());memory={k:int(memory_stat[k]) for k in ['anon','shmem','kernel']};memory['nonreclaimable_estimate']=sum(memory.values())
report={'schema':'union1509_source_only_storage_feasibility_v1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'contributor':'Codex / lean_integration_successor','status':'SOURCE_COMPATIBLE_STANDARD_CLOUD_FULL_AUDIT_BLOCKED_BY_UNCHANGED_ABORT_BUDGET_NO_CONTEXT_OR_PRODUCER',
 'bindings':{'source_identity_delta':pin(DELTA),'existing_plan':pin(W/'RESOURCE-AND-RUN-PLAN.json'),'reader':pin(Path(__file__)),'cache_header_projection':pin(projection),'natural141_formal_acceptance':pin(L/'G6-NATURAL-COMMON-FOREST-FACTORIZATION-141-ACCEPTANCE-20261011T0202Z.json'),'base1504_certificate':pin(L/'HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json'),'base1504_raw_owned_audit':pin(run/'attempts/00002-OwnedAudit/work/AUDIT-RESULT.json')},
 'source_composition':{'base1504':1504,'accepted_new_source_versions':[{k:r[k] for k in ['module','sha256','path','imports']} for r in delta['genuinely_new_modules']],'new_unique':5,'prospective1509_modules':1509,'guard_modules_extra':0,'shared_source_import_conflicts':0,'global_Main_modules_added':0,'combined_decl_count_not_predicted_as_observed':True},
 'static_cache_observation':{'existing_completed_header_paths':1509,'base_headers':1504,'separate_scoped_headers':5,'all_selected_source_hashes_and_compiler_native_headers_match':True,'all_cached_object_paths_exist':True,'provider_selection_header_projection_is_not_new_cache_or_materialization':True,'all_companion_current_hashes_direct_import_context_key_recomputation_and_install_guards_still_required_before_any_future_admission':True,'actual1509_cache_admissions':0,'fresh_source_recompiles_requested':0,'future_proof_work_if_budgeted':'All1509 authenticated components reused subject to unchanged exact admission checks; only aggregate and complete owned audit fresh.'},
 'resource_snapshot':{'allocation_roots':roots,'root_count':26,'lstat':lstat,'conservative_followed':follow,'memory':memory,'memory_abort_bytes':plan['memory_abort_bytes'],'scratch_abort_bytes':abort,'scratch_hard_limit_bytes':hard,'lstat_headroom_to_abort':abort-lstat['allocated_bytes'],'conservative_headroom_to_abort':abort-follow['allocated_bytes'],'overlay_free_bytes':os.statvfs('/workspace').f_bavail*os.statvfs('/workspace').f_frsize,'tmp_free_bytes':os.statvfs('/tmp').f_bavail*os.statvfs('/tmp').f_frsize},
 'empirical_single_copy_profile':{'source_run':str(run),'owned_raw_bytes':114300292,'allocation_by_category':profile,'other_run_metadata_rows':sorted(rows,key=lambda r:r['bytes'],reverse=True),'borrowed_imported_object_tree_entirely_excluded':True,'old_raw_loader_files_excluded_from_new_required_profile':True,'two_gzip_capture_reserve_bytes':native_reserve,'most_favorable_existing_full_run_profile_before_all_preparation_export_growth_QA_and_git_bytes':best_tested,'deficit_vs_current_conservative_abort_headroom_before_preparation_export_growth_QA_and_git':max(0,best_tested-(abort-follow['allocated_bytes'])),'qualification':'This is an observed full1504 profile, not a theorem that every future1509 output has a size lower bound. It is the smallest demonstrated standard profile with all originals retained and no speculative evidence reduction.'},
 'conservative_standard_new_context_reserve':{'reserves':reserves,'total_bytes':reserve,'current_lstat_plus_reserve':lstat['allocated_bytes']+reserve,'current_followed_plus_reserve':follow['allocated_bytes']+reserve,'deficit_lstat_to_abort':max(0,lstat['allocated_bytes']+reserve-abort),'deficit_followed_to_abort':max(0,follow['allocated_bytes']+reserve-abort),'fits_lstat_abort':lstat['allocated_bytes']+reserve<abort,'fits_conservative_abort':follow['allocated_bytes']+reserve<abort,'compiler_resource_limits_not_changed':True,'connected_aggregate_and_audit_unchanged_cap_memory_mib':6144,'connected_aggregate_and_audit_unchanged_cap_seconds':300,'ordinary_unchanged_cap_memory_mib':4096,'ordinary_unchanged_cap_seconds':180},
 'publication_pool_observation':{'path':str(pool),'actual_object_count':len(pool_sizes),'actual_compressed_content_bytes':sum(r[0] for r in pool_sizes),'actual_allocated_file_bytes':sum(r[1] for r in pool_sizes),'included_in_both_root_measurements':True,'old64MiB_quota_bytes':64*MIB,'root_reported_source_only_correction96MiB_bytes':96*MIB,'root_correction_is_not_compiler_launch_approval':True,'natural71row73file_export_pending_bytes':4672092,'future_git_growth32MiB_planning_allowance_condition':'Only if Root separately approves96MiB policy and bounds remaining new object padding/inputs; this is an additional conservative storage sensitivity, not a quota change by this reader.','with_additional32MiB_git_growth_followed_bound':follow['allocated_bytes']+reserve+32*MIB},
 'lossless_storage_options':{'same_filesystem_source_cache_companion_hardlinks':'Prospective unchanged authenticated installer/seeder. All immutable original paths, receipts, keys and hashes retained; EXDEV copies require independent budget and pre/post hashes. No input chmod/delete.','no_second_raw_audit':'Existing accepted copy/literal producer may operate only after an actual independent raw1509 audit exists; restore is streaming hash/comparison, optional output disabled. No second114MB base/target and no synthetic prospective records.','codec_limits':'Existing128MiB raw file bound covers observed114300292B base. Future actual target/pins/gzip cap require separately frozen plan and root byte-trial approval; existing fixed168 trials are not rerun.','export':'Fixed complete shmem bytes plus explicit manifests; base1504 portablegzip and actual target delta may reduce publication bytes, but cannot remove the compiler-produced raw target or current raw run metadata. EightMiB overlay reserve retained; no overlay copy presumed.','in_place_old_artifact_mutation':'Forbidden; none performed.'},
 'resumable_integration_plan':{'preferred_after_new_main_terminal1568_notice':'Root/Rust independently authenticate delivered1568 source/import/audit/native/projection scope; recheck all1504 overlapping records plus the exact five consumers, then hand this five-source topological set to that existing owner for prospective1573. No cloud64 replay and no redundant1509 raw audit.','new_source_topological_order':delta['safe_new_only_topological_order'],'peer_terminal_packet_status':'Root reports newest main397285 delivered accepted1568 terminal packet. Independent saved review and exact current graph compatibility are separate pending gates at this observation. Earlier live-only delta metadata is retained as dated history.','external_native_receipts_not_promoted_to_cloud_cache':True,'different_external_native_digest_requires_own_same-host_component_checks_for_the_five_sources':True,'fresh1573_aggregate_and_complete_ownership_audit_still_required':True,'cloud1509_resume_condition':'Fresh measured conservative prior allocation plus all exact retained output/preparation/export/publication reserves must fall below unchanged2013265920 abort. Otherwise keep source-owner handoff and preserved scoped acceptances; no trial or cap raise.'},
 'execution':{'builder_or_Lean_module_imported':False,'compiler_evaluator_native_or_audit_producer_launched':False,'new_context_cache_or_source_stage_created':False,'old_accepted_source_cache_attempt_receipt_audit_bytes_written_moved_deleted_or_relabelled':False,'mathematical_or_master_acceptance_promoted':False}}
save(OUT/'SOURCE-ONLY-UNION1509-FEASIBILITY.json',report)
print(json.dumps({'report':pin(OUT/'SOURCE-ONLY-UNION1509-FEASIBILITY.json'),'projection':pin(projection),'reader':pin(Path(__file__)),'root_count':len(roots),'lstat':lstat['allocated_bytes'],'followed':follow['allocated_bytes'],'best_tested_profile':best_tested,'deficit_conservative_best_tested':report['empirical_single_copy_profile']['deficit_vs_current_conservative_abort_headroom_before_preparation_export_growth_QA_and_git'],'standard_new_reserve':reserve,'standard_deficit_followed':report['conservative_standard_new_context_reserve']['deficit_followed_to_abort'],'status':report['status']}))
