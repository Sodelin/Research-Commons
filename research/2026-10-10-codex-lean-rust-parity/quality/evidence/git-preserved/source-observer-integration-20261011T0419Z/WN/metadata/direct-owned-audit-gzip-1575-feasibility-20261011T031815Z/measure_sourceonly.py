#!/usr/bin/env python3
"""Source-only measurements; never imports a builder, stages, or runs Lean/native/Git writes."""
import datetime,gzip,hashlib,json,os,subprocess
from pathlib import Path
N=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
F=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
A=Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z')
R=Path('/workspace/Research-Commons');P=R/'research/2026-10-10-codex-lean-rust-parity';D=Path(__file__).parent
OLD=N/'metadata/static-union1573-source-plan-20261011T022330.460416Z'
THIN=N/'metadata/static-union1575-thin-source-plan-20261011T024500Z'
PROJECTION=N/'metadata/union1509-source-only-feasibility-20261011T0208Z/EXISTING-CACHE-HEADER-PROJECTION-1509.json'
COMMIT='62020166e3e7ef690838f50b13caa149ede419ec'
PKG='research/2026-10-11-dot-accepted-connected-union1570-g4span-0225z'
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir']
LOCAL_NATIVE='6f8ad181b1b3b832d74cf0f88255b519a3512252c343d3e0cde0c540cbfe7aac'
BINARY='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474'
memo={}
def digest(b):return hashlib.sha256(b).hexdigest()
def sha(p):
 p=Path(p);s=p.stat();k=(s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns)
 if k not in memo:
  h=hashlib.sha256()
  with p.open('rb') as f:
   while b:=f.read(1048576):h.update(b)
  memo[k]=h.hexdigest()
 return memo[k]
def identity(p):
 p=Path(p);s=p.stat();return {'path':str(p),'sha256':sha(p),'bytes':s.st_size}
def read(p):return json.loads(Path(p).read_bytes())
def pinned(p,h):
 assert sha(p)==h,(str(p),'input pin drift');return read(p)
def gb(path):
 env={**os.environ,'GIT_OPTIONAL_LOCKS':'0'}
 return subprocess.check_output(['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-C',str(R),'show',COMMIT+':'+path],env=env)
def companion(p,s):return p.with_suffix(s) if s in ('.olean','.ilean','.ir') else Path(str(p)+s[len('.olean'):])
def bundle(p):return {s:sha(companion(p,s)) for s in SUFFIXES if companion(p,s).is_file()}
def measure(roots,follow):
 seen=set();total=0
 for root in roots:
  for directory,_,files in os.walk(root):
   for p in [Path(directory),*(Path(directory)/n for n in files)]:
    s=p.stat() if follow else p.lstat();k=(s.st_dev,s.st_ino)
    if k not in seen:seen.add(k);total+=s.st_blocks*512
 return {'allocated_bytes':total,'distinct_device_inode_count':len(seen)}
def freeze_set():
 return {str(p):sha(p) for folder in (OLD,THIN) for p in sorted(folder.iterdir()) if p.is_file()}
pre=freeze_set();assert len(pre)==17
plan=pinned(N/'RESOURCE-AND-RUN-PLAN.json','2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c')
thin=pinned(THIN/'STATIC-PROSPECTIVE-UNION1575-SOURCE-PLAN-DELTA.json','fdd1bd064539d4f15f835efc7531e40ee3cb659166a853555f960aa018ac06c3')
oldmap=pinned(OLD/'STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json','8b65e62c0d894269d73429035c40a006c877d88d76a4543edd3300630ae73878')['modules']
warm=pinned(PROJECTION,'6bbec498d8210ecc4bd30334bd7ae826ecd3ac9aec89fa9627d03011f20ec4d2');wm={r['module']:r for r in warm};assert len(wm)==1509
base=pinned(A/'DEPENDENCY-GRAPH.json','e05a87db2b34f42aada87a958f7ff9114c68a817458b5919f7ecac62386fbacd')['targets']['current/connected']
pg=gb(PKG+'/DEPENDENCY-GRAPH.json');assert digest(pg)==thin['source_inputs']['peer_graph_sha256'];peer=json.loads(pg)['targets']['current/connected']
mb=gb(PKG+'/MANIFEST.json');assert digest(mb)==thin['source_inputs']['peer_manifest_sha256'];manifest=json.loads(mb)
files={r['path']:r for r in manifest['files']}
cold=sorted(set(peer['modules'])-set(base['modules']));assert len(cold)==66
assert all(peer['modules'][m]['sha256']==e['sha256'] and peer['modules'][m]['imports']==e['imports'] for m,e in base['modules'].items())
new5=sorted(set(wm)-set(base['modules']));assert len(new5)==5 and not(set(new5)&set(peer['modules']))
rb=gb(PKG+'/evidence/RESULT.projected.json.gz');assert digest(rb)==files['evidence/RESULT.projected.json.gz']['sha256'];pr=json.loads(gzip.decompress(rb))
components=pr['component_receipts'];peer_native=sorted({r['native_runtime_digest'] for r in components});assert len(components)==1570 and len(peer_native)==1 and peer_native!=[LOCAL_NATIVE]
context=A/'.build/runs/20261010T223805.816906Z/targets/current_connected/objects'
math=Path('/workspace/dependencies/mathlib4');binroot=Path('/workspace/toolchains/lean-4.33.1-linux/bin')
external=sorted((math/'.lake/packages').glob('*/.lake/build/lib/lean'))+[math/'.lake/build/lib/lean',binroot.parent/'lib/lean']
def lookup(m):
 package=m.split('.')[0];rel=m.replace('.','/')+'.olean'
 for root in [context]+external:
  if (root/package).is_dir() or (root/(package+'.olean')).exists():return root/rel
 raise FileNotFoundError(m)
external_names=sorted({i for e in peer['modules'].values() for i in e['imports'] if i not in peer['modules']})
external_rows=[]
for m in external_names:
 p=lookup(m);assert p.is_file(),('missing external first-namespace object',m,p)
 external_rows.append({'module':m,'path':str(p),'artifacts':bundle(p)})
assert len(external_names)==181
recs={};objects={};bundle_rows=[];own_inodes={};five=[];all_sizes=[];key_mismatches=[]
for row in warm:
 m=row['module'];p=Path(row['receipt']['path']);assert sha(p)==row['receipt']['sha256'];rec=read(p)
 assert rec['module']==m and rec['source_sha256']==row['source_sha256'] and rec['compiler_sha256']==BINARY and rec['mathlib_commit']==MATHLIB and rec['native_runtime_digest']==LOCAL_NATIVE and rec['exit_code']==0 and rec['status'].startswith('PASS')
 obj=p.parent/'artifact.olean';actual=bundle(obj);assert actual==rec['object_artifacts'],('staged object mismatch',m)
 kd={'module':m,'source':row['source_sha256'],'compiler':BINARY,'mathlib':MATHLIB,'trust':0,'kernel_check':True,'imports':rec['direct_import_artifacts'],'native_runtime_digest':LOCAL_NATIVE,'artifact_boundary':'olean-private-server-ilean-ir-native-v3'}
 if m=='ThetaCertificate5' and row['source_sha256']=='e541af41b215cf473e63d4e968fdc42b31fe74f6384387f66de61f1ebbd7fbab':kd['resource_exception']={'memory_mib':6144,'seconds':600}
 if digest(json.dumps(kd,sort_keys=True).encode())!=row['cache_key']:key_mismatches.append(m)
 size=0
 for suffix in actual:
  q=companion(obj,suffix);s=q.stat();assert s.st_dev==D.stat().st_dev
  size+=s.st_size;own_inodes[(s.st_dev,s.st_ino)]=(s.st_size,s.st_blocks*512)
  bundle_rows.append([m,suffix,str(q),actual[suffix],s.st_size,s.st_blocks*512,s.st_dev,s.st_ino])
 all_sizes.append(size);recs[m]=rec;objects[m]=obj
 if m in new5:five.append({'module':m,'receipt':identity(p),'physical_staged_object':str(obj),'cache_key':row['cache_key'],'bundle_bytes':size,'bundle':actual})
assert not key_mismatches,key_mismatches
checked_imports=0;import_mismatches=[]
for m,rec in recs.items():
 for i,expected in rec['direct_import_artifacts'].items():
  actual=bundle(objects[i] if i in objects else lookup(i));checked_imports+=1
  if actual!=expected:import_mismatches.append([m,i])
assert not import_mismatches,import_mismatches
searched=set();cache_header_count=0;cold_headers=[];unparsed=0
cache_search_roots=[str(Path(x)/'.build/cache') for x in plan['allocation_roots']]+[str(P/'lean/.build')]
for search in cache_search_roots:
 if not Path(search).exists():continue
 for directory,_,names in os.walk(search):
  if 'receipt.json' not in names:continue
  p=Path(directory)/'receipt.json';s=p.stat();k=(s.st_dev,s.st_ino)
  if k in searched:continue
  searched.add(k);cache_header_count+=1
  try:r=read(p)
  except (ValueError,UnicodeDecodeError):unparsed+=1;continue
  m=r.get('module')
  if m in cold and r.get('source_sha256')==peer['modules'][m]['sha256']:
   cold_headers.append({'module':m,'receipt':identity(p),'native':r.get('native_runtime_digest'),'compiler':r.get('compiler_sha256'),'status':r.get('status')})
# No cache is admitted; this is a bounded header search and current bundle observation.
cold_sources=[]
for m in cold:
 e=peer['modules'][m];entry=oldmap.get(m)
 if entry is not None:
  size=entry['bytes'];origin=entry['source_git_path']
 else:
  entry=next(r for r in thin['two_peer_G4_records'] if r['module']==m);size=entry['bytes'];origin=entry['source_git_path']
 b=gb(origin);assert digest(b)==e['sha256'] and len(b)==size
 cold_sources.append({'module':m,'sha256':e['sha256'],'bytes':size,'git_path':origin})
native=pinned(A/'.build/runs/20261010T223805.816906Z/NATIVE-RUNTIME-PINS.json',sha(A/'.build/runs/20261010T223805.816906Z/NATIVE-RUNTIME-PINS.json'))
assert native['native_runtime_digest']==LOCAL_NATIVE
for p,e in native['libraries'].items():assert sha(p)==e['sha256']
assert digest(json.dumps({p:e['sha256'] for p,e in native['libraries'].items()},sort_keys=True).encode())==LOCAL_NATIVE
assert sha(binroot/'lean')==BINARY
run=A/'.build/runs/20261010T223805.816906Z';profile={'raw_audit':{},'other_metadata_allocated_bytes':0,'aggregate_object_allocated_bytes':0}
raws=list(run.rglob('AUDIT-RESULT.json'));assert len(raws)==1
raw=raws[0];profile['raw_audit']={**identity(raw),'allocated_bytes':raw.stat().st_blocks*512}
seen=set()
for p in run.rglob('*'):
 if not p.is_file() or p.is_symlink():continue
 if any(x in p.parts for x in ('objects','obj')) or p==raw or 'native-loader' in p.name:continue
 if any(str(p).endswith(s) for s in SUFFIXES):continue
 s=p.stat();k=(s.st_dev,s.st_ino)
 if k not in seen:seen.add(k);profile['other_metadata_allocated_bytes']+=s.st_blocks*512
agg=run/'targets/current_connected/attempts' # Only named aggregate companions below actual attempt directories.
for p in run.rglob('*.olean'):
 if 'aggregate' in str(p).lower() and 'objects' not in p.parts:profile['aggregate_object_allocated_bytes']+=p.stat().st_blocks*512
contracts=[P/'lean/scripts/build_connected.py',P/'lean/scripts/AuditTemplate.lean',P/'lean/scripts/evidence_distribution.py',P/'lean/scripts/preserve_connected_result.py',N/'scripts/storage_wrapper.py',N/'scripts/build_with_authenticated_overlay.py',N/'scripts/build_with_mathlib_overlay.py',N/'scripts/guard_natural_common_20261011.py',P/'rust/audit_copy_literal_codec.py',P/'rust/audit_portable_restore.py',binroot.parent/'src/lean/Init/System/IO.lean']
roots=plan['allocation_roots'];lstat=measure(roots,False);followed=measure(roots,True)
mem={k:int(v) for k,v in (line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())}
pool=F/'metadata/git-object-pool-preserved-20261011';poolfiles=[p for p in pool.rglob('*') if p.is_file()];ps={}
for p in poolfiles:
 s=p.stat();ps[(s.st_dev,s.st_ino)]=(s.st_size,s.st_blocks*512)
post=freeze_set();assert pre==post
sizes=sorted(all_sizes)
out={'schema':'source_only_direct_owned_audit_gzip1575_measurements_v1','status':'SOURCE_ONLY_NOT_RUN_AUTHORIZATION','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reader':identity(__file__),'reader_predecessor':{'raw_sha256':'34cd270eb06d28eb7be0a39dae497b1943996563ce0ec1047bef49925307b46b','gzip':identity(D/'measure_sourceonly_v1.py.gz'),'failure':'Wrong metadata filename PUBLICATION-MANIFEST.json; failed before companion measurements; corrected to exact peer MANIFEST.json. No scientific input, old artifact or policy changed.'},'inputs':{'plan':identity(N/'RESOURCE-AND-RUN-PLAN.json'),'warm_projection':identity(PROJECTION),'thin1575':identity(THIN/'STATIC-PROSPECTIVE-UNION1575-SOURCE-PLAN-DELTA.json'),'public1570_review':identity(thin['source_inputs']['public1570_saved_review']['path']),'base1504_graph':identity(A/'DEPENDENCY-GRAPH.json'),'peer_graph':{'commit':COMMIT,'git_path':PKG+'/DEPENDENCY-GRAPH.json','sha256':digest(pg)},'peer_result':{'git_path':PKG+'/evidence/RESULT.projected.json.gz','sha256':digest(rb)}},'local_warm_observations':{'components':len(warm),'same_filesystem_current_staged_files':len(bundle_rows),'unique_artifact_inodes':len(own_inodes),'unique_artifact_bytes':sum(s[0] for s in own_inodes.values()),'unique_artifact_allocated_bytes':sum(s[1] for s in own_inodes.values()),'companion_observation_rows_sha256':digest(json.dumps(bundle_rows,separators=(',',':')).encode()),'cache_keys_recomputed':len(warm),'exact_direct_import_bundle_observations':checked_imports,'five_paths':five,'current_native_libraries_rehashed':len(native['libraries']),'compiler_sha256':BINARY,'native_runtime_digest':LOCAL_NATIVE,'admission':False,'qualification':'Current selected headers and staged bundles observed; no future Builder admission, kernel replay, import, installation, namespace construction, or native process. New context must repeat full strict checks.'},'cold_peer_components':{'count':len(cold),'source_bytes':sum(x['bytes'] for x in cold_sources),'source_identity_rows_sha256':digest(json.dumps(cold_sources,separators=(',',':')).encode()),'source_sizes':{x['module']:x['bytes'] for x in cold_sources},'peer_native_runtime_digest':peer_native[0],'local_native_runtime_digest':LOCAL_NATIVE,'object_companion_sizes_in_public_receipts':False,'known_cache_search_roots':{'counted_roots':len(roots),'suffix':'.build/cache','additional':str(P/'lean/.build')},'distinct_receipt_headers_read':cache_header_count,'unparsed_receipts':unparsed,'exact_source_headers_found':cold_headers,'locally_compatible_exact_source_headers':sum(r['native']==LOCAL_NATIVE and r['compiler']==BINARY for r in cold_headers),'qualification':'No claim about unsearched external hosts or private peer objects. Public projected receipts do not authorize local cache reuse.'},'external_first_namespace_observations':{'count':len(external_rows),'missing':0,'rows_sha256':digest(json.dumps(external_rows,separators=(',',':')).encode()),'existing_context':str(context),'external_roots':[str(x) for x in external],'future_complete_namespace_and_native_checks_required':True},'actual_full1504_profile':profile,'resources':{'allocation_roots':roots,'count':len(roots),'distinct_inode_lstat':lstat,'conservative_followed':followed,'scratch_hard_bytes':plan['scratch_hard_limit_bytes'],'scratch_abort_bytes':plan['scratch_abort_bytes'],'distinct_abort_headroom_bytes':plan['scratch_abort_bytes']-lstat['allocated_bytes'],'followed_abort_headroom_bytes':plan['scratch_abort_bytes']-followed['allocated_bytes'],'memory_nonreclaimable_bytes':sum(mem.get(x,0) for x in ('anon','shmem','kernel')),'memory_abort_bytes':plan['memory_abort_bytes'],'git_object_pool':{'path':str(pool),'unique_files':len(ps),'content_bytes':sum(x[0] for x in ps.values()),'allocated_bytes':sum(x[1] for x in ps.values()),'content_cap_bytes':100663296,'remaining_content_bytes':100663296-sum(x[0] for x in ps.values())}},'contract_source_pins':[identity(p) for p in contracts],'frozen_static_artifacts':{'files':len(pre),'pre_post_unchanged':True,'path_hash_rows_sha256':digest(json.dumps(pre,sort_keys=True).encode())},'prohibited_actions_performed':[]}
out['second_reader_predecessor']={'raw_sha256':'04e0e7afa0d00d205f92da084879b64c2e1b4f6e6494e24937e8c696968d990a','gzip':identity(D/'measure_sourceonly_v2.py.gz'),'failure':'Wrong peer RESULT targets schema; failed before companion measurements. Corrected to exact component_receipts; scope and policies unchanged.'}
(D/'MEASUREMENTS.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
print(json.dumps({'status':out['status'],'warm':len(warm),'staged_files':len(bundle_rows),'direct_bundle_checks':checked_imports,'cold':len(cold),'cold_cache_headers':len(cold_headers),'metadata_alloc':profile['other_metadata_allocated_bytes'],'distinct':lstat['allocated_bytes'],'followed':followed['allocated_bytes'],'report':str(D/'MEASUREMENTS.json')}))
