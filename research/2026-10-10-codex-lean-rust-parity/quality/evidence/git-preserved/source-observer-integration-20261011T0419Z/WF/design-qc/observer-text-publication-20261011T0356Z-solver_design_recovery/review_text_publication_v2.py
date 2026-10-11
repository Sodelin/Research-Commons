#!/usr/bin/env python3
"""Own source and saved-byte QC; no target imports, Git calls or producers.
Contributor: /root/solver_design_recovery. Full original hold remains beside
this source. Uses authenticated OWN prior stdlib byte-reader definitions only.
"""
import argparse, ast, datetime, difflib, hashlib, json, os, resource, stat, zlib
from pathlib import Path, PurePosixPath

resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2))
W=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
D=W/'metadata/new-source-observer-publication-20261011T0348Z'
Q=Path(__file__).parent
MAX_OWN=32768
PUB='9970fdb3088e4f441aa162191ac4cdb30dfe8df5794e1f5f3edc71fdb28a9f1c'
OLD='b1a5fa14db3a05b71dcc13c15a435614742b531cbee39a6d9ad7e489b068467f'
HEAD='4862b9618ca422da4ad5381b5dec0a3fcac56e76'
TREE='145eefb4baaec4eafca16622ed9fdfb538313922'
BASE_POOL=99789839
def sha(b):return hashlib.sha256(b).hexdigest()
def canon(x):return sha(json.dumps(x,sort_keys=True,separators=(',',':')).encode())
def pin(path,h=None,size=None):
 p=Path(path);b=p.read_bytes();d={'path':str(p),'bytes':len(b),'sha256':sha(b)}
 assert h is None or d['sha256']==h,('hash',str(p))
 assert size is None or len(b)==size,('bytes',str(p))
 return d,b
def own_alloc():return sum(p.lstat().st_blocks*512 for p in [Q,*Q.iterdir()])
def save(name,r):
 raw=(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n').encode()
 assert len(raw)<=8192,('receipt_size',len(raw))
 assert own_alloc()+((len(raw)+4095)//4096)*4096<=MAX_OWN
 out=Q/name
 with out.open('xb') as f:f.write(raw)
 print(json.dumps({'status':r['status'],'receipt':pin(out)[0],'reader':pin(__file__)[0],'own_allocated_including_directory':own_alloc()},sort_keys=True))
def source():
 oi,o=pin(D/'publish_reviewed_text.py',OLD,9087)
 pi,p=pin(D/'publish_reviewed_text_v2.py',PUB,9104)
 before="rows.extend([row(G,m['prefix']+'/FUNDING-GATE.json'),row(pathlib.Path(review_path),m['prefix']+'/INDEPENDENT-PUBLICATION-QC.json')])\n    for x in rows:"
 after="extra=[row(G,m['prefix']+'/FUNDING-GATE.json'),row(pathlib.Path(review_path),m['prefix']+'/INDEPENDENT-PUBLICATION-QC.json')]\n    rows.extend(extra)\n    for x in extra:"
 assert o.decode().count(before)==1 and o.decode().replace(before,after)==p.decode()
 patch=''.join(difflib.unified_diff(o.decode().splitlines(True),p.decode().splitlines(True),fromfile='publish_reviewed_text.py',tofile='publish_reviewed_text_v2.py'))
 di,db=pin(D/'EXACT-OWN-PUBLISHER-V2-CORRECTION.patch');assert db==patch.encode()
 ci,cb=pin(D/'OWN-PUBLISHER-PREAPPLY-SOURCE-HOLD-CORRECTION.json');c=json.loads(cb)
 assert c['original_sha256']==OLD and c['corrected_sha256']==PUB and c['target_or_git_mutations'] is False
 hi,hb=pin(Q/'ORIGINAL-PUBLISHER-SOURCE-HOLD.json','c5ff533fdf0de99e6cb853ad8558857d43a8d502ac1ce44a557ab53de81003e4',1205)
 assert json.loads(hb)['status']=='HOLD_BEFORE_MUTATION_DUPLICATE_FUTURE_ENTRY_INSERTION'
 trees=[ast.parse(x) for x in (o,p)];functions=[{n.name:n for n in x.body if isinstance(n,ast.FunctionDef)} for x in trees]
 assert set(functions[0])==set(functions[1])
 changed=[n for n in functions[0] if ast.dump(functions[0][n])!=ast.dump(functions[1][n])];assert changed==['apply']
 text=p.decode()
 for s in ("review['funding_gate_sha256']==sha(G.read_bytes())","assert sha(raw)==g['base_index_sha256']","assert A.pool()==BASE_POOL","funding(r,b,t,a)","with OUT.open('xb')","assert observed==entries","assert A.git('write-tree').decode().strip()==future","assert after['pool_bytes']<=BASE_POOL+b+t","assert not q.active_markers(roots)"):
  assert s in text,s
 assert text.index('b,t,a,future=costs(rows+[rx],entries);funding(r,b,t,a)')<text.index('for x in rows:write_blob(x)')
 assert text.count("A.git('write-tree')")==1
 ai,ab=pin(D.parent/'git-evidence-publication/publish_exact_compressed_checkpoint_20261011.py','c3479b7fcc3cc57e7485c7fdd6fa6fb4beef3b89c0a0ae046737ff879eeb6a24',13800)
 gi,gb=pin(D.parent/'source-only-observer-execution-guard-20261011T0338Z/guard_erased_selected_observer_v1.py','e7416c8012edf64a4f84cf24c98bc79d22d070cf8f71008f9a080462edf3e723',27217)
 assert "b.decode('utf-8')" in ab.decode() and "not p.is_symlink()" in ab.decode()
 return {'original_source':oi,'publisher_source':pi,'full_exact_patch':di,'root_correction':ci,'own_original_full_hold':hi,'base_helper':ai,'accounting_guard':gi,'only_changed_function':'apply','full_source_review':'All original rows enter prospective entries once; only extra Gate/QC rows are then inserted. Gate/QC and complete future actual receipt are costed before any mutation. All prior stage entries, every full blob/100644/S row and one final tree are read back. Existing encoding retained only after full body authentication; new writes require exact zlib6 length. Imported helpers are pinned; QC never imports them. Fixed96MiB/26roots/2GiB/1.875GiB/15GiB/8MiB floor remain. Linux accounting import executes definitions only, not target processes. Root owns all mutation and launch/failure preservation.'}
def own_byte_library():
 p=W/'design-qc/exact-publication-recovery-v3-20261011T0302Z-solver_design_recovery/review_partial_and_recovery_v3.py'
 i,b=pin(p,'807dbe710f49944badb8c5c7d64a5d65709333651800bafc31e1c72a9e15cd67',32482)
 prefix=b.split(b'\ndef jp(',1)[0];ns={'__file__':str(p),'__name__':'own_saved_byte_definitions'}
 exec(compile(prefix,str(p),'exec'),ns)
 return i,ns
def normalized(p):
 assert isinstance(p,str) and p and not p.startswith('/') and '\\' not in p and all(ord(c)>=32 for c in p)
 assert str(PurePosixPath(p))==p and '..' not in PurePosixPath(p).parts
def blob(source_path,destination,n=None,h=None):
 normalized(destination);s=Path(source_path);assert s.is_file() and not s.is_symlink()
 i,b=pin(s,h,n);b.decode('utf8');assert not b.startswith(b'\x7fELF')
 full=b'blob '+str(len(b)).encode()+b'\0'+b
 return {'source_path':str(s),'git_tree_path':destination,'bytes':len(b),'sha256':sha(b),'git_blob':hashlib.sha1(full).hexdigest(),'zlib6_content_bytes':len(zlib.compress(full,6))}
def inclusive_allocation(roots):
 seen=set();seen_targets=set();raw=followed=symlink_dirs=0
 for r in roots:
  assert Path(r).is_dir()
  for d,ds,fs in os.walk(r,followlinks=False):
   paths=[Path(d)]+[Path(d)/f for f in fs]+[Path(d)/n for n in ds if (Path(d)/n).is_symlink()]
   for p in paths:
    before=p.lstat();key=before.st_dev,before.st_ino
    if key not in seen:seen.add(key);raw+=before.st_blocks*512
    stats=[before]
    if stat.S_ISLNK(before.st_mode):
     s=p.stat()
     if stat.S_ISREG(s.st_mode):stats.append(s)
     elif stat.S_ISDIR(s.st_mode):symlink_dirs+=before.st_blocks*512
    for s in stats:
     key=s.st_dev,s.st_ino
     if key not in seen_targets:seen_targets.add(key);followed+=s.st_blocks*512
 return {'lstat':raw,'lstat_plus_regular_file_targets':followed,'conservative':max(raw,followed),'directory_symlink_blocks':symlink_dirs}
def funding(args,protocol):
 mi,mb=pin(D/'INPUTS.json',args.manifest_sha);m=json.loads(mb)
 gi,gb=pin(D/'FUNDING-GATE.json',args.gate_sha);g=json.loads(gb)
 assert m['publisher_sha256']==g['publisher_sha256']==PUB
 assert m['base_head']==g['base_head']==HEAD and m['base_tree']==g['base_tree']==TREE
 assert g['manifest_sha256']==mi['sha256'] and g['status']=='READY_SEPARATELY_FUNDED_TEXT_REQUIRES_INDEPENDENT_QC'
 assert g['base_pool_bytes']==BASE_POOL
 assert (g['blob_reserve'],g['tree_reserve'],g['commit_reserve'],g['allocation_reserve'])==(524288,131072,16384,6291456)
 assert BASE_POOL+524288+131072+16384==100461583<100663296
 lib,ns=own_byte_library();idxraw=ns['INDEX'].read_bytes();idx,imeta=ns['index_entries'](idxraw);stage=ns['stage_bytes'](idx)
 assert sha(stage)==g['base_index_sha256'] and ns['current_head']()==HEAD
 assert ns['commit_tree'](HEAD)[0]==TREE
 entries={p:(format(v['mode'],'o'),v['git_blob']) for p,v in idx.items()}
 assert all(v['stage']==0 for v in idx.values())
 current,ct=ns['encode_tree'](entries);assert current==TREE
 rows=[blob(r['source_path'],r['git_tree_path'],r['bytes'],r['sha256']) for r in m['files']]
 rows.append(blob(D/'INPUTS.json',m['prefix']+'/INPUT-MANIFEST.json'))
 paths=[r['git_tree_path'] for r in rows];assert len(paths)==len(set(paths))==g['known_rows']
 reserved=[m['prefix']+'/'+x for x in ('FUNDING-GATE.json','INDEPENDENT-PUBLICATION-QC.json','ACTUAL-PUBLICATION.json')]
 assert len(set(reserved))==3 and not (set(paths)&set(reserved))
 for r in rows:
  p=r['git_tree_path'];assert p not in idx and not os.path.lexists(ns['REPO']/p)
  entries[p]=('100644',r['git_blob'])
 future,ts=ns['encode_tree'](entries)
 unique={r['git_blob']:r for r in rows if not ns['object_present'](r['git_blob'])}
 mt={oid:(body,n) for oid,body,n in ts if not ns['object_present'](oid)}
 b=sum(r['zlib6_content_bytes'] for r in unique.values());t=sum(n for body,n in mt.values())
 a=sum(((r['zlib6_content_bytes']+4095)//4096)*4096+4096 for r in unique.values())+sum(((n+4095)//4096)*4096+4096 for body,n in mt.values())
 assert (b,t,a)==(g['known_blob_content_bytes'],g['known_tree_content_bytes'],g['known_loose_allocation_bytes'])
 assert b<=524288 and t<=131072 and a+262144<=6291456
 cp,cb=pin('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/RESOURCE-AND-RUN-PLAN.json','2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c',4477)
 cfg=json.loads(cb);roots=cfg['allocation_roots'];assert len(roots)==len(set(roots))==26
 assert g['resource']['ordered26_roots']==roots and g['resource']['resource_config_sha256']==cp['sha256']
 assert (cfg['scratch_hard_limit_bytes'],cfg['scratch_abort_bytes'],cfg['memory_abort_bytes'])==(2147483648,2013265920,16106127360)
 pool=ns['POOLS'][0];assert pool.resolve().is_relative_to(W)
 pool_bytes=sum(p.stat().st_size for p in pool.rglob('*') if p.is_file());assert pool_bytes==BASE_POOL
 usage=inclusive_allocation(roots);remaining=MAX_OWN-own_alloc()
 assert usage['conservative']+remaining+6291456<2013265920
 memory=dict(s.split() for s in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())
 nr=sum(int(memory[k]) for k in ('anon','shmem','kernel'));assert nr<16106127360
 markers=[str(Path(r)/'ACTIVE-GUARDED-PROCESS.json') for r in roots if (Path(r)/'ACTIVE-GUARDED-PROCESS.json').exists()];assert not markers
 tmp=ns['free_bytes']('/tmp');overlay=ns['free_bytes']('/workspace')
 assert tmp>len(idxraw)+2097152 and overlay>8388608
 native,_=pin('/dev/shm/rc-source-fit-native-20261010T221453.635194Z/target/debug/source-fit-solver','443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00',4292856)
 assert not (D/'ACTUAL-PUBLICATION.json').exists()
 return {'schema':'independent_fixed_text_publication_funding_qc_v2','status':'PASS_FIXED_V2_SOURCE_ALL_FROZEN_ROWS_AND_CURRENT_SEPARATE_FUNDING','publisher_sha256':PUB,'manifest_sha256':mi['sha256'],'funding_gate_sha256':gi['sha256'],'reviewer':'/root/solver_design_recovery','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reader':pin(__file__)[0],'protocol':protocol,'own_byte_library':lib,'manifest':mi,'gate':gi,'all_rows':{'count':len(rows),'full_original_bytes':sum(r['bytes'] for r in rows),'row_binding_canonical_sha256':canon(rows),'all_utf8_regular_non_ELF':True,'normalized_absent_unique_paths':True,'reserved_gate_QC_receipt_paths_absent':True},'index':{'current_physical':imeta,'all_prior_stage_entries_sha256':sha(stage),'all_entries_count':len(idx),'HEAD':HEAD,'tree':TREE,'known_future_tree':future},'known_exact_cost':{'missing_unique_blobs':len(unique),'missing_unique_trees':len(mt),'blob_content_bytes':b,'tree_content_bytes':t,'loose_alloc_bytes':a,'missing_tree_binding_canonical_sha256':canon(sorted([oid,n] for oid,(body,n) in mt.items()))},'capacity':{'pool_current_bytes':pool_bytes,'full_funded_pool_bytes':100461583,'fixed_pool_limit':100663296,'global':usage,'remaining_own_Q_allowance':remaining,'full6MiB_plus_remaining_Q_projected':usage['conservative']+remaining+6291456,'global_abort':2013265920,'global_hard':2147483648,'nonreclaimable':nr,'nonreclaimable_abort':16106127360,'tmp_free':tmp,'index_plus2MiB':len(idxraw)+2097152,'overlay_free':overlay,'overlay_floor':8388608,'markers':markers,'resource_configuration':cp,'protected_public':native,'fresh_preapply_remeasurement_required':True},'late_exact_callback':'Apply must hash this actual frozen QC, append Gate/QC and serialize the full actual receipt, predict the ONE final tree and exact missing zlib6 bytes, then repeat both512KiB/128KiB quotas and full6MiB/26root funding before ANY object/index/receipt mutation. Known prepare cost is not the final apply cost; no guessed receipt/tree subreserve.', 'scope':'Full listed scientific/source/runtime UTF8 bytes preserved as supplied; publication itself does not prove claims, remote completion, source/typed encoding/refinement, arbitrary Code Old, global factorization, new G4 formalization or combined1575 kernel. Native result rows are saved evidence only, no rerun. Source v1 and complete own/root preapply HOLD/correction records retained. Root owns all index/HEAD/object/publication mutation.','target_import_producer_native_Git_or_overlay_operations':False,'same_index_and_pool_must_be_held_until_root_apply':True,'own_cap_bytes_including_directory':MAX_OWN}

ap=argparse.ArgumentParser();ap.add_argument('--source-only',action='store_true');ap.add_argument('--manifest-sha');ap.add_argument('--gate-sha');args=ap.parse_args()
protocol=source()
if args.source_only:
 save('V2-PUBLISHER-SOURCE-PROTOCOL-QC.json',{'schema':'independent_fixed_publisher_v2_source_protocol_qc','status':'PASS_FIXED_V2_SOURCE_PROTOCOL_ONLY_M_G_REQUIRED_BEFORE_MUTATION','reviewer':'/root/solver_design_recovery','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'publisher_sha256':PUB,'reader':pin(__file__)[0],'protocol':protocol,'manifest_gate_current_index_pool_capacity_review_pending':True,'target_import_producer_native_Git_or_overlay_operations':False,'own_cap_bytes_including_directory':MAX_OWN})
else:
 assert args.manifest_sha and args.gate_sha and len(args.manifest_sha)==len(args.gate_sha)==64
 save('V2-PUBLISHER-FROZEN-INPUTS-FUNDING-QC.json',funding(args,protocol))
