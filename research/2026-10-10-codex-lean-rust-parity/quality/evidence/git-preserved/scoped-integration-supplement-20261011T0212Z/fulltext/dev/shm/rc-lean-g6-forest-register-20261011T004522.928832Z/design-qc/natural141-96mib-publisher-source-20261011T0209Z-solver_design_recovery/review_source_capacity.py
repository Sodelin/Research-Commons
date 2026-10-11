"""Independent source/preserved-byte/capacity review; no Git or target import."""
import ast,copy,hashlib,json,os
from pathlib import Path
from datetime import datetime,timezone
W=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
N=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
B=W/'metadata/git-evidence-publication';Q=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h=None):
 got=sha(p);assert h is None or got==h,str(p)
 return {'path':str(p),'bytes':p.stat().st_size,'sha256':got}
parent=B/'publish_natural141_pass_fixed_shmem_to_git_20261011.py'
new=B/'publish_natural141_pass_fixed_shmem_to_git_20261011_v2_96mib.py'
policy=B/'GIT-EVIDENCE-ALLOCATION-POLICY-CORRECTION-20261011T0207Z.json'
pins=[pin(parent,'ccb2353c8c02323e0840215772d3a10ffbd406fa9c1bb0865d0c71d41071eea3'),pin(new,'7b464ff41bd45bca4a9356ebbb00c0193f8e8af3d34da9fc5ef023a07eac2218'),pin(policy,'b06d2a7d91998320f51779f59895f3987025964e73f2254a8565398cfe56d02b'),pin(W/'design-qc/natural141-pass-publisher-source-20261011T0200Z-solver_design_recovery/NATURAL141-PASS-PUBLISHER-SOURCE-QC-ATTEMPT1.json','15217f2f3588d0cc266ebb178a759d9ace9bcf034aa5c4aa6b7d48c8e251b2aa')]
p=json.loads(policy.read_bytes());a,z=ast.parse(parent.read_bytes()),ast.parse(new.read_bytes())
assert len(a.body)==len(z.body)
outputs=[]
for x,y in zip(a.body,z.body):
 if isinstance(x,ast.Assign) and isinstance(y,ast.Assign) and len(x.targets)==len(y.targets)==1 and isinstance(x.targets[0],ast.Name) and isinstance(y.targets[0],ast.Name) and x.targets[0].id==y.targets[0].id=='OUT':
  assert isinstance(y.value,ast.Call) and y.value.args[0].value==str(B/'NATURAL141-PASS-PUBLICATION-V2-96MIB.json')
  outputs.append(ast.unparse(y.value));x.value=copy.deepcopy(y.value)
assert len(outputs)==1
quota=[]
for n in ast.walk(a):
 if isinstance(n,ast.Assert) and ast.unparse(n.test) in ("before['object_pool_bytes'] + payload + len(rows) * 4096 < 64 * 1024 * 1024","after['object_pool_bytes'] < 64 * 1024 * 1024"):
  vals=[v for v in ast.walk(n.test.comparators[0]) if isinstance(v,ast.Constant) and v.value==64];assert len(vals)==1
  vals[0].value=96;quota.append(ast.unparse(n.test))
assert len(quota)==2 and ast.dump(a)==ast.dump(z),'Only two opaque evidence quota constants and OUT may change'
assert p['old_git_evidence_pool_limit_bytes']==64*1024*1024 and p['new_git_evidence_pool_limit_bytes']==96*1024*1024
assert p['global_scratch_hard_limit_bytes']==2*1024**3 and p['global_scratch_abort_bytes']==15*1024**3//8 and p['global_memory_abort_bytes']==15*1024**3
assert p['compiler_kernel_native_scientific_acceptance_changed'] is False and p['no_data_deleted'] and p['no_producer_launched']
planpath=N/'RESOURCE-AND-RUN-PLAN.json';pins.append(pin(planpath,'2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c'))
plan=json.loads(planpath.read_bytes())
assert p['allocation_roots']==plan['allocation_roots'] and len(p['allocation_roots'])==len(set(p['allocation_roots']))==26
assert (plan['scratch_hard_limit_bytes'],plan['scratch_abort_bytes'],plan['memory_abort_bytes'])==(p['global_scratch_hard_limit_bytes'],p['global_scratch_abort_bytes'],p['global_memory_abort_bytes'])
monitor=Path(plan['monitor_path']);pins.append(pin(monitor,'8a190dfa60b0151c1ad622fab21eefac866b44145a1d0d3665b31f66a1979a9b'))
assert "['anon', 'shmem', 'kernel']" in monitor.read_text()
pool=Path('/tmp/rc-cloud-git-objects-20261010T223739.438030Z');assert pool.is_symlink() and pool.resolve()==W/'metadata/git-object-pool-preserved-20261011'
assert any(pool.resolve().is_relative_to(Path(r)) for r in p['allocation_roots'])
oldpath=B/'GIT-OBJECT-POOL-LOSSLESS-RELOCATION-20261011.json';pins.append(pin(oldpath));old=json.loads(oldpath.read_bytes())
assert old['objects_count']==len(old['rows'])==2261 and old['content_bytes']==55754823
for row in old['rows']:
 f=pool/row['path'];assert f.stat().st_size==row['bytes'] and sha(f)==row['sha256']
incoming=[]
for row in p['incoming_pack_files']:
 f=Path(row['path']);item=pin(f,row['sha256']);assert item['bytes']==row['bytes'] and f.resolve().is_relative_to(pool.resolve());incoming.append(item)
assert len(incoming)==3 and sum(r['bytes'] for r in incoming)==16568966
files=[]
for f in sorted(pool.rglob('*')):
 if not f.is_file():continue
 assert not f.is_symlink()
 s=f.stat();files.append({'relative':str(f.relative_to(pool)),'bytes':s.st_size,'allocated_bytes':s.st_blocks*512,'sha256':sha(f)})
content=sum(r['bytes'] for r in files);allocated_pool=sum(r['allocated_bytes'] for r in files)
assert content==p['pool_current_bytes']==73080592 and content-sum(r['bytes'] for r in incoming)==56511626
prior=json.loads((W/'design-qc/natural141-pass-publisher-source-20261011T0200Z-solver_design_recovery/NATURAL141-PASS-PUBLISHER-SOURCE-QC-ATTEMPT1.json').read_bytes())
assert prior['dated_capacity_observation']['object_pool_content_bytes']==content-16568966
r=N/'G6-NATURAL-COMMON-FACTORIZATION-PROOF141-20261011T014055.249073Z-RESULT.json';pins.append(pin(r,'6db53e2eba1679cae6841cf1e2c6ffc37cd3d985873d0f8d73a8e2c17094bf30'))
result=json.loads(r.read_bytes());export=Path(result['complete_lossless_export_original'])
assert len(result['preserved_files'])==71 and result['packet_distribution_complete'] is False
assert (export/'PRESERVATION-MANIFEST.json').read_bytes()==r.read_bytes()
for row in result['preserved_files']:
 f=export/row['path'];assert f.stat().st_size==row['bytes'] and sha(f)==row['sha256']
actual=[f for f in export.rglob('*') if f.is_file()];assert len(actual)==p['natural_pass_file_count']==73
payload=sum(f.stat().st_size for f in actual);assert payload==p['natural_pass_payload_bytes']==4672092
object_growth=payload+len(actual)*4096;assert object_growth==p['conservative_natural_pass_object_growth_bytes']==4971100
reserve=p['supplemental_object_reserve_bytes'];assert reserve==8*1024*1024
seen=set();allocated=0;roots=[]
for root in p['allocation_roots']:
 rootpath=Path(root);assert rootpath.is_dir();markers=[]
 for name in ('G6-NATURAL-RUN-IN-PROGRESS.json','LEAN-RUN-IN-PROGRESS.json','RUN-IN-PROGRESS.json'):
  if (rootpath/name).exists():markers.append(name)
 assert not markers,(root,markers)
 addition=0
 for directory,dirs,names in os.walk(rootpath):
  for f in [Path(directory),*(Path(directory)/name for name in names)]:
   st=f.lstat();key=(st.st_dev,st.st_ino)
   if key not in seen:seen.add(key);allocated+=st.st_blocks*512;addition+=st.st_blocks*512
 roots.append({'path':root,'distinct_inode_allocated_contribution_bytes':addition})
values=dict(line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())
nonreclaim={k:int(values[k]) for k in ('anon','shmem','kernel')};mem=sum(nonreclaim.values())
free=lambda f:os.statvfs(f).f_bavail*os.statvfs(f).f_frsize
index=Path('/tmp/rc-cloud-git-index-20261010T224217.512566Z/INDEX-CURRENT')
assert content>64*1024*1024,'Preserved imported pack actually invalidates old opaque pool quota'
assert content+object_growth+reserve<96*1024*1024
assert allocated+object_growth+reserve<p['global_scratch_abort_bytes']<p['global_scratch_hard_limit_bytes']
assert mem+object_growth+reserve<p['global_memory_abort_bytes']
assert free('/tmp')>object_growth+index.stat().st_size+2*1024*1024 and free('/workspace')>8*1024*1024
report={'schema':'natural141_git_evidence_96mib_quota_source_capacity_design_qc_v1','contributor':'Codex / solver_design_recovery','observed_utc':datetime.now(timezone.utc).isoformat(),'status':'PASS_SOURCE_ONLY_EXACT_OPAQUE_EVIDENCE_QUOTA_CORRECTION_WITH_COUNTED_CAPACITY','reviewer_sha256':sha(Path(__file__)),'pins':pins,'exact_source_changes':{'quota_assertions':quota,'output_receipt_binding':outputs,'whole_AST_otherwise_literal_equal':True},'incoming_peer_commit_reported_by_policy':p['incoming_peer_commit'],'incoming_pack_files':incoming,'pool_preserved_old_records_rehashed':2261,'pool_current_files':files,'pool_current_file_count':len(files),'pool_content_bytes':content,'pool_file_allocated_bytes':allocated_pool,'allocation_roots':roots,'capacity':{'roots':26,'independent_guard_compatible_lstat_allocated_bytes':allocated,'policy_dated_lstat_allocated_bytes':p['distinct_inode_allocated_bytes'],'current_nonreclaimable_components':nonreclaim,'current_nonreclaimable_bytes':mem,'policy_dated_nonreclaimable_bytes':p['nonreclaimable_bytes'],'funded_natural_pass_growth_bytes':object_growth,'supplement_reserve_bytes':reserve,'projected_funded_pool_content_bytes':content+object_growth+reserve,'new_pool_content_cap_bytes':96*1024*1024,'projected_funded_global_allocated_bytes':allocated+object_growth+reserve,'global_scratch_abort_bytes':p['global_scratch_abort_bytes'],'global_scratch_hard_limit_bytes':p['global_scratch_hard_limit_bytes'],'global_memory_abort_bytes':p['global_memory_abort_bytes'],'tmp_free_bytes':free('/tmp'),'index_bytes':index.stat().st_size,'overlay_free_bytes':free('/workspace')},'qualification':['Justified opaque Git evidence allocation-policy correction preserves the incoming canonical pack and current proof/export bytes. Imported mathematical identities/peer kernel or coherent union acceptance are outside this review.','Only current73-file publication and8MiB supplement are funded at this dated observation. Future publication/producer slots must remeasure all roots, reserve exact resources and enforce unchanged global caps.','Source contains retained absent-path/index/object/blob byte checks and all8MiB floors. Root alone executes; immediate current source/result/path/index/resource checks and terminal producer verification remain required.','Old ccb64MiB source/failed readiness remain immutable and unrun. No producer, compiler, target helper, Git mutation, or overlay write by reviewer.'],'git_commands_or_target_producers_started':0,'overlay_writes':0}
out=Q/'NATURAL141-96MIB-PUBLISHER-SOURCE-CAPACITY-QC-ATTEMPT1.json'
with out.open('x') as f:json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps({'receipt':str(out),'sha256':sha(out),'status':report['status'],'counts':len(files),'capacity':report['capacity']}))
