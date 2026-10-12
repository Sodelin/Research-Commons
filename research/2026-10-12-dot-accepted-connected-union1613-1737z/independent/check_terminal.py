"""Independent terminal evidence read/hash verifier. Never invokes Lean/Lake/builders."""
from pathlib import Path
import gzip,hashlib,json,re,time,sys
P=Path(sys.argv[1]);N=Path('LOCAL_EVIDENCE/g4-paired493-check-20261012-1646z');B=Path('LOCAL_EVIDENCE/connected-union1611-20261012-1239z');O=Path(__file__).parent
rd=lambda p:json.loads(p.read_bytes());memo={};totalbytes=0
H=lambda b:hashlib.sha256(b).hexdigest()
def sha(p):
 global totalbytes
 p=p.resolve(strict=True);s=p.stat();key=(str(p),s.st_size,s.st_mtime_ns,s.st_ctime_ns)
 if key not in memo:
  hh=hashlib.sha256()
  with p.open('rb') as f:
   for z in iter(lambda:f.read(1048576),b''):hh.update(z);totalbytes+=len(z)
  memo[key]=hh.hexdigest()
 return memo[key]
def check(p,h):assert sha(p)==h,(str(p),'hash')
SUFFIX=['.olean','.olean.private','.olean.server','.ilean','.ir']
def bundle(p):return {s:sha(p.with_suffix(s) if s in ['.olean','.ilean','.ir'] else Path(str(p)+s[len('.olean'):])) for s in SUFFIX if (p.with_suffix(s) if s in ['.olean','.ilean','.ir'] else Path(str(p)+s[len('.olean'):])).is_file()}
start=time.monotonic();prep=rd(P/'PREPARATION.json');assert prep['graph_sha256']=='768e587ffb189b3700aa4acc82853dcced49477b80c028d70e055d40cf65ff13';
for n,h in prep['scripts'].items():check(P/'scripts'/n,h)
assert prep['scripts']['run_aggregate1613.py']=='22e27e17fba13e87bd647f18a05898c66b262533482a13499f41269db5cfd1ec';assert prep['scripts']['build_aggregate1613.py']=='bc0617b521ef3c6812ab6932f00536bfad3a8c66d82bdeb9b2e129de834b1f7d'
f=rd(P/'.build/LATEST-RUN.json');assert f['status']=='PASS_ALL_REQUESTED_TARGETS';run=Path(f['run']);assert f==rd(run/'FINAL-RECEIPT.json');assert f['counts'].get('cache_reuse')==1613 and f['counts'].get('fresh_components',0)==0 and set(f['counts'])<=set(['cache_reuse','fresh_components']);target='current/connected';assert f['targets_requested']==f['targets_passed']==[target]
g=rd(P/'DEPENDENCY-GRAPH.json');assert sha(P/'DEPENDENCY-GRAPH.json')==f['graph_sha256']==prep['graph_sha256'];t=g['targets'][target];mods=t['modules'];assert len(mods)==1613
tr=rd(run/'targets/current_connected/RESULT.json');assert tr['status']=='PASS' and tr['closure_modules']==1613;records=tr['component_receipts'];by={r['module']:r for r in records};assert len(records)==len(by)==1613 and set(by)==set(mods)
source_names=set(mods)-set(rd(B/'DEPENDENCY-GRAPH.json')['targets']['current/connected']['modules']);assert len(source_names)==2;contexts=run/'targets/current_connected/objects';native=rd(run/'NATIVE-RUNTIME-PINS.json');nf=rd(run/'NATIVE-RUNTIME-FINAL-REHASH.json');assert nf['stable'] and nf['compiler_identity_stable'];assert f['native_runtime_final_rehash_stable'] and f['compiler_identity_stable'];assert nf['hashes']=={p:v['sha256'] for p,v in native['libraries'].items()};assert H(json.dumps(nf['hashes'],sort_keys=True).encode())==f['native_runtime_digest']==native['native_runtime_digest'];assert nf['compiler_sha256']==f['compiler_sha256']==f['compiler_final_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
for p,d in nf['hashes'].items():check(Path(p),d)
for n,e in mods.items():check(P/'source-store'/(e['sha256']+'.lean'),e['sha256'])
index=rd(P/'trace-transport/INDEX.json');trace={str(P/e['raw_path']):e for e in index['entries']};tracebytes=0

def verify_fresh(r,kind,source,imports,obj):
 global tracebytes
 rp=Path(r['receipt_directory'])/'receipt.json';raw=rd(rp);assert raw=={k:v for k,v in r.items() if k not in ['cached_object','audit_output']};assert rp.parents[2]==run
 assert r['status']=='PASS_FRESH_KERNEL_CHECK' and r['exit_code']==0 and r['kind']==kind and r['source_and_imports_stable'];assert r['native_runtime_stat_stable'] and r['native_initialized_libraries_bound'];assert r['native_runtime_digest']==f['native_runtime_digest'];assert r['source_sha256']==H(source);assert r['cap_seconds']==300 and r['cap_memory_mib']==6144
 cmd=r['command'];check(Path(cmd[0]),f['compiler_sha256']);assert cmd[1:4]==['-j1','-t0','-M6144'] and '-Ddebug.skipKernelTC=false' in cmd
 frozen=Path(r['working_directory'])/(r['module'].replace('.','/')+'.lean');assert frozen.read_bytes()==source
 for name in ['stdout','stderr']:check(rp.parent/name,r[name+'_sha256']);assert b'sorryAx' not in (rp.parent/name).read_bytes()
 assert set(r['direct_import_bindings'])==set(imports)
 for q,v in r['direct_import_bindings'].items():
  assert bundle(Path(v['path']))==v['artifacts']==r['direct_import_artifacts'][q];assert v['sha256']==r['direct_import_sha256'][q]==v['artifacts']['.olean']
  if q in by:assert v['artifacts']==by[q]['object_artifacts']
 used=set()
 for item in r['native_loader_outputs']:
  path=Path(item['path']);e=trace.get(str(path))
  if e:
   assert str(P/e['receipt_path'])==str(rp);check(rp,e['receipt_sha256']);arc=P/e['archive_path'];check(arc,e['archive_sha256']);data=gzip.decompress(arc.read_bytes());assert len(data)==e['raw_bytes'] and H(data)==e['raw_sha256']==item['sha256']
  else:data=path.read_bytes();assert H(data)==item['sha256']
  tracebytes+=len(data);used|={str(Path(x.decode()).resolve()) for x in re.findall(rb'calling init:\s*(/[^\s]+)',data)}
 assert used==set(r['native_initialized_libraries']);assert all(r['native_initialized_libraries'][x]==native['libraries'][x] for x in used)
 if obj:assert bundle(Path(cmd[-2]))==r['object_artifacts'] and r['object_sha256']==r['object_artifacts']['.olean'];assert cmd[-3]=='-o'
 else:assert '-o' not in cmd

for n,r in by.items():
 assert r['source_sha256']==mods[n]['sha256'];assert bundle(contexts/(n.replace('.','/')+'.olean'))==bundle(Path(r['cached_object']))==r['object_artifacts'];key={'module':n,'source':r['source_sha256'],'compiler':f['compiler_sha256'],'mathlib':f['mathlib_commit'],'trust':0,'kernel_check':True,'imports':r['direct_import_artifacts'],'native_runtime_digest':f['native_runtime_digest'],'artifact_boundary':'olean-private-server-ilean-ir-native-v3'}
 if n=='ThetaCertificate5':key['resource_exception']={'memory_mib':6144,'seconds':600}
 cachekey=H(json.dumps(key,sort_keys=True).encode());assert rd(P/'.build/cache'/cachekey/'receipt.json')==r
 assert r==rd((N if n in source_names else B)/'.build/cache'/cachekey/'receipt.json')
aggregate=('\n'.join('import '+n for n in t['roots'])+'\n').encode();template=(P/'scripts/AuditTemplate.lean').read_text();audit=aggregate+template.replace('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]','#'+json.dumps(t['order'])).replace('"AUDIT-OWNED.json"','"AUDIT-RESULT.json"').encode();(O/'GENERATED-SOURCE-PINS.json').write_text(json.dumps({'aggregate_sha256':H(aggregate),'audit_source_sha256':H(audit)},indent=2)+'\n');verify_fresh(tr['aggregate_receipt'],'aggregate',aggregate,t['roots'],True);ar=tr['audit_receipt'];verify_fresh(ar,'complete-owned-audit',audit,t['roots']+['Lean.Util.CollectAxioms'],False)
meta=ar['audit_transport'];assert meta['status']=='COMPLETE_VERIFIED_AUDIT_BYTES' and meta['child_exit_code']==0;check(Path(meta['archive_path']),meta['gzip_sha256']);data=gzip.decompress(Path(meta['archive_path']).read_bytes());assert H(data)==meta['raw_sha256'] and len(data)==meta['raw_bytes']<=512*2**20;a=json.loads(data);assert a['selected_modules']==t['order'];assert not a['owned_axioms'] and not a['nonstandard_axiom_rows'] and not a['missing_modules'];assert a['declaration_count']==len(a['declarations'])==len({x['name'] for x in a['declarations']});assert sum(x['kind']=='theorem' for x in a['declarations'])==a['theorem_declaration_count']
# Restore exact accepted1611 audit directly from its receipt-bound archive.
br=rd(B/'.build/runs/20261012T124232.521572Z/targets/current_connected/RESULT.json');bt=br['audit_receipt']['audit_transport'];p=Path(bt['archive_path']);check(p,bt['gzip_sha256']);raw=gzip.decompress(p.read_bytes());assert H(raw)==bt['raw_sha256']=='258ada41a6190d7392968d5ad863b5f532b50d0cbd81444627ae62623451c59b' and len(raw)==bt['raw_bytes'];old=json.loads(raw);before={x['name']:x for x in old['declarations']};after={x['name']:x for x in a['declarations']};changed=[{'name':n,'before':before[n],'after':v} for n,v in after.items() if n in before and before[n]!=v];new=[v for n,v in after.items() if n not in before];retained=sum(n in before for n in after);assert len(before)==103706 and set(before)<=set(after)
spfiles=list(P.glob('SUPERVISOR-*.json'));sp=[(p,rd(p)) for p in spfiles if rd(p)['status']=='TERMINAL_EXIT_ZERO'];assert len(sp)==1;spfile,sp=sp[0];assert sp['limit_event'] is None and sp['exit_code']==0 and sp['allocation_limit_bytes']==3*2**30 and sp['free_floor_bytes']==8*2**30;assert sp['peak_path_counted_allocated_bytes']<3*2**30 and sp['minimum_observed_free_bytes']>=8*2**30 and sp['minimum_observed_available_memory_bytes']>=2**30
assert len(list((run/'attempts').iterdir()))==2
result={'status':'TERMINAL_INTEGRITY_CHECK_PASS_METADATA_COMPARISON_REQUIRES_REVIEW' if changed else 'TERMINAL_INTEGRITY_AND_RETAINED_METADATA_PASS','run':run.name,'graph_sha256':f['graph_sha256'],'checked_new_source_hashes':{n:mods[n]['sha256'] for n in sorted(source_names)},'exact_accepted1611_cache_receipts':1611,'exact_accepted_new_cache_receipts':2,'fresh_components_in_final_run':0,'new_sources_checked_across_prior_493_attempts':2,'fresh_aggregate_and_full_audit':True,'declarations':a['declaration_count'],'theorems':a['theorem_declaration_count'],'audit_raw_sha256':meta['raw_sha256'],'audit_raw_bytes':meta['raw_bytes'],'retained_prior_names':retained,'changed_prior_records':changed,'globally_new_names':len(new),'globally_new_theorems':sum(x.get('kind')=='theorem' for x in new),'new_records':new,'supervisor_receipt_sha256':sha(spfile),'supervisor':sp,'fresh_native_trace_bytes_verified':tracebytes,'hash_checked_files':len(memo),'hash_checked_bytes':totalbytes,'elapsed_seconds':time.monotonic()-start,'reviewer_invoked_compiler':False}
(O/'TERMINAL-EVIDENCE-CHECK.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['new_records','changed_prior_records','supervisor']},indent=2));print('changed names',[x['name'] for x in changed])

expected_new=rd(Path('LOCAL_EVIDENCE/paired493-independent-review-20261012-1638z/NEW-DECLARATIONS.json'));expected={x['name']:x for x in expected_new};actual={x['name']:x for x in new};assert not changed and retained==103706 and actual==expected and len(actual)==658
comparison={'status':'PASS_LITERAL_FULL_BASELINE_AND_EXACT_NARROW_ADDITIONS','prior_records':103706,'literal_retained_records':retained,'changed_records':0,'deleted_records':0,'new_records_exact_to_narrow':len(actual),'narrow_metadata_qualifications_used_as_waivers':False,'new_kind_counts':{k:sum(x['kind']==k for x in new) for k in sorted({x['kind'] for x in new})},'expected_new_records_sha256':sha(Path('LOCAL_EVIDENCE/paired493-independent-review-20261012-1638z/NEW-DECLARATIONS.json'))}
(O/'LITERAL-RECORD-COMPARISON.json').write_text(json.dumps(comparison,indent=2)+'\n');print(json.dumps(comparison,indent=2))
