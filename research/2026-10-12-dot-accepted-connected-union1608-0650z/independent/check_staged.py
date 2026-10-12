"""Read-only source/cache/native/import/allocation preflight; never invokes compiler or builder."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time,sys
P=Path(sys.argv[1]);B=Path('LOCAL_EVIDENCE/connected-union1607-20261012-0558z');N=Path('LOCAL_EVIDENCE/g4-legal-panel317-check-20261012-0632z');Q=Path('LOCAL_EVIDENCE/union1608-budget-proposal-20261012-0639z');O=Path(__file__).parent
LB=Path('LOCAL_EVIDENCE/lean-restoration-20261010-2311z/lean-4.33.1-linux/bin');ML=Path('LOCAL_EVIDENCE/lean-restoration-20261010-2311z/mathlib')
BIN='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550';MC='0df444a360eaa60ab8c11dca51a86af692955474';GS='98dec131ae2d5c262bf5cf1ece59501316dda6bd00572bc8a7c09688a5babf49';TARGET='current/connected';SUFFIX=['.olean','.olean.private','.olean.server','.ilean','.ir'];start=time.monotonic();memo={};hashed=0
read=lambda p:json.loads(p.read_bytes())
def sha(p):
 global hashed
 p=p.resolve(strict=True);s=p.stat();key=(str(p),s.st_size,s.st_mtime_ns,s.st_ctime_ns)
 if key not in memo:
  hh=hashlib.sha256()
  with p.open('rb') as f:
   for z in iter(lambda:f.read(1048576),b''):hh.update(z);hashed+=len(z)
  memo[key]=hh.hexdigest()
 return memo[key]
def check(p,d):assert sha(p)==d,(str(p),'hash mismatch')
def companion(p,s):return p.with_suffix(s) if s in ['.olean','.ilean','.ir'] else Path(str(p)+s[len('.olean'):])
def bundle(p):return {s:sha(companion(p,s)) for s in SUFFIX if companion(p,s).is_file()}
check(Q/'STAGING-INPUT-PINS.json','2266a27c3c71b169a2e7ba09fa046b1d9c713d61a3ee4ffedbabfaed6ff46f4d');pins=read(Q/'STAGING-INPUT-PINS.json');check(Q/'prepare_aggregate1608.py','ab1c127328eff37a73b6ccd071c338d21bd45d57f69e5c48b32ab74aa8c4d410');check(O/'INDEPENDENT-PROFILE-REVIEW.md','74ce7079704741a8d937c3afbf2df2915a8ffa63eba6e8b55c9b3697d16d51c5')
check(P/'DEPENDENCY-GRAPH.json',GS);g=read(P/'DEPENDENCY-GRAPH.json');t=g['targets'][TARGET];mods=t['modules'];assert len(mods)==1608;oldg=read(B/'DEPENDENCY-GRAPH.json');old=oldg['targets'][TARGET]['modules'];assert len(old)==1607
for k,v in oldg['targets'].items():assert g['targets']['history/accepted1607' if k==TARGET else k]==v
for n,e in old.items():assert mods[n]==e
owned_old={m:e['sha256'] for m,e in old.items() if m.startswith('Mathlib.')};assert len(owned_old)==11 and {m:e['sha256'] for m,e in mods.items() if m.startswith('Mathlib.')}==owned_old
new={'G4ActualLegalPanelComb':'4fd78fc530e103512f4dc98a7e60ac2d592ad666e7feac17b5ab1456f1a961c9'};allmods={};inherited=set();seen=set()
for v in g['targets'].values():
 for n,e in v['modules'].items():
  if n in allmods:assert (e['sha256'],e['imports'])==(allmods[n]['sha256'],allmods[n]['imports'])
  allmods[n]=e
assert len(allmods)==1609 and set(mods)-set(old)==set(new)
for n,e in allmods.items():
 f=P/'source-store'/(e['sha256']+'.lean');check(f,e['sha256']);assert f.is_file() and not f.is_symlink();origin=(N if n in new else B)/'source-store'/(e['sha256']+'.lean');check(origin,e['sha256']);s=origin.stat();inherited.add((s.st_dev,s.st_ino));assert (f.stat().st_dev,f.stat().st_ino)==(s.st_dev,s.st_ino)
 if n in new:assert e['sha256']==new[n]
for n in t['order']:
 assert n not in seen
 for q in mods[n]['imports']:assert q not in mods or q in seen
 seen.add(n)
assert seen==set(mods)
prep=read(P/'PREPARATION.json');assert prep['scripts']==pins['scripts'];assert prep['graph_sha256']==GS and prep['selected_count']==1608 and prep['reuse_count']==1608 and prep['fresh_count']==0 and prep['source_store_count']==1609 and prep['owned_mathlib_count']==11
for n,h in pins['scripts'].items():assert not (P/'scripts'/n).is_symlink();check(P/'scripts'/n,h)
for n,h in pins['config'].items():check(P/n,h);check(B/n,h)
check(LB/'lean',BIN);assert subprocess.check_output(['git','-C',str(ML),'rev-parse','HEAD'],text=True).strip()==MC
linked=subprocess.check_output(['ldd',str(LB/'lean')],text=True);libraries={Path(x).resolve() for x in re.findall(r'(/[^\s()]+)',linked) if Path(x).is_file()}|{p.resolve() for p in (LB.parent/'lib').rglob('*.so*') if p.is_file()}|{p.resolve() for p in (ML/'.lake').rglob('*.so*') if p.is_file()}
nr=read(B/'.build/runs/20261012T060008.240388Z/NATIVE-RUNTIME-PINS.json');assert {str(p) for p in libraries}==set(nr['libraries']);current_native={str(p):sha(p) for p in sorted(libraries)};assert current_native=={p:v['sha256'] for p,v in nr['libraries'].items()};nd=hashlib.sha256(json.dumps(current_native,sort_keys=True).encode()).hexdigest();assert nd==nr['native_runtime_digest']
inputs=read(P/'AUTHENTICATED-REUSE-INPUTS.json');assert set(inputs)==set(allmods);by={};receipts=[]
for n,row in inputs.items():
 cp=P/'.build/cache'/row['key'];rp=cp/'receipt.json';check(rp,row['receipt_sha256']);assert rp.read_bytes()==((N if n in new else B)/'.build/cache'/row['key']/'receipt.json').read_bytes();r=read(rp);by[n]=r
 assert r['module']==n and r['source_sha256']==allmods[n]['sha256'];assert r['status']=='PASS_FRESH_KERNEL_CHECK' and r['kind']=='component' and r['exit_code']==0;assert r['source_and_imports_stable'] and r['native_runtime_stat_stable'] and r['native_initialized_libraries_bound'];assert r['compiler_sha256']==BIN and r['mathlib_commit']==MC and r['native_runtime_digest']==nd
 cap=(600,6144) if n=='ThetaCertificate5' else (180,4096);assert (r['cap_seconds'],r['cap_memory_mib'])==cap and r['command'][1:4]==['-j1','-t0','-M'+str(cap[1])] and '-Ddebug.skipKernelTC=false' in r['command'];assert bundle(cp/'artifact.olean')==bundle(Path(r['cached_object']))==r['object_artifacts']
 for f in row['files']:
  origin=Path(f['path']);staged=cp/f['name'];check(origin,f['sha256']);check(staged,f['sha256']);s=origin.stat();inherited.add((s.st_dev,s.st_ino));assert (staged.stat().st_dev,staged.stat().st_ino)==(s.st_dev,s.st_ino)
 k={'module':n,'source':r['source_sha256'],'compiler':BIN,'mathlib':MC,'trust':0,'kernel_check':True,'imports':r['direct_import_artifacts'],'native_runtime_digest':nd,'artifact_boundary':'olean-private-server-ilean-ir-native-v3'}
 if n=='ThetaCertificate5':k['resource_exception']={'memory_mib':6144,'seconds':600}
 assert hashlib.sha256(json.dumps(k,sort_keys=True).encode()).hexdigest()==row['key'];receipts.append({'module':n,'cache_key':row['key'],'receipt_sha256':sha(rp),'object_artifacts':r['object_artifacts']})
external=sorted((ML/'.lake/packages').glob('*/.lake/build/lib/lean'))+[ML/'.lake/build/lib/lean',LB.parent/'lib/lean']
def lookup(m):
 package=m.split('.')[0]
 for root in external:
  if (root/package).is_dir() or (root/(package+'.olean')).exists():
   q=root/(m.replace('.','/')+'.olean');assert q.is_file(),('first namespace missing file',m);return q
 raise AssertionError(('missing external namespace',m))
count=0;extbindings={}
for n,r in by.items():
 assert set(r['direct_import_bindings'])==set(allmods[n]['imports'])==set(r['direct_import_artifacts'])
 for q,v in r['direct_import_bindings'].items():
  expected=v['artifacts'];assert expected==r['direct_import_artifacts'][q] and v['sha256']==expected['.olean']==r['direct_import_sha256'][q];assert bundle(Path(v['path']))==expected
  if q in by:assert by[q]['object_artifacts']==expected
  else:actual=lookup(q);assert bundle(actual)==expected;extbindings[q]={'resolved_path':str(actual.resolve()),'artifacts':expected}
  count+=1
for q in t['external_imports']:
 actual=lookup(q);extbindings[q]={'resolved_path':str(actual.resolve()),'artifacts':bundle(actual)}
newalloc=pathbytes=extra=0;inos=set();largest=0
for f in [P]+list(P.rglob('*')):
 s=f.lstat();key=(s.st_dev,s.st_ino)
 if f.is_file() and not f.is_symlink():pathbytes+=s.st_blocks*512;largest=max(largest,s.st_size)
 else:extra+=s.st_blocks*512
 if key not in inherited and key not in inos:newalloc+=s.st_blocks*512;inos.add(key)
budget=read(P/'STAGING-BUDGET.json');check(P/'LAUNCH-RECORDED.py','e27a5afdec0e120ed609709b455f9fb96af8ac36bc1cb67f2795362b34a621fb');launch_alloc=(P/'LAUNCH-RECORDED.py').stat().st_blocks*512;assert budget=={'new_nonshared_allocated_bytes':newalloc-launch_alloc,'path_counted_file_bytes':pathbytes-launch_alloc,'directory_symlink_allocated_bytes':extra};assert newalloc<=64*2**20 and pathbytes<=1024*2**20 and largest<512*2**20
assert not (P/'.build/LATEST-RUN.json').exists();assert set(p.parent.name for p in (P/'.build/cache').glob('*/receipt.json'))=={v['key'] for v in inputs.values()}
active=[]
for f in Path('/proc').glob('[0-9]*/comm'):
 try:
  name=f.read_text().strip();status=(f.parent/'status').read_text()
  if name in ['lean','lake'] and not re.search(r'^State:\s+Z',status,re.M):active.append({'pid':int(f.parent.name),'name':name})
 except (FileNotFoundError,PermissionError,ProcessLookupError):pass
assert not active,active
free=shutil.disk_usage(P).free;mem=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024;assert free>11*2**30 and mem>=7*2**30
result={'status':'INDEPENDENT_STAGED1608_PREFLIGHT_PASS_NO_COMPILER','checked_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'graph_sha256':GS,'source_modules_selected':1608,'source_store_and_cache_contexts':1609,'literal_accepted1607_selected_contexts':1607,'literal_checked_new_contexts':1,'isolated_fixture_contexts':1,'fresh_unchecked_sources':0,'current_native_libraries':len(current_native),'current_native_digest':nd,'direct_import_bundles_checked':count,'external_import_modules_checked':len(extbindings),'current_exact_compiler_sha256':BIN,'current_mathlib_commit':MC,'complete_official_and_eleven_owned_mathlib_namespace_retained':True,'staged_script_pins':pins['scripts'],'staged_config_pins':pins['config'],'original_staging_allocation':budget,'current_allocation_with_recording_launcher':{'new_nonshared_allocated_bytes':newalloc,'path_counted_file_bytes':pathbytes,'directory_symlink_allocated_bytes':extra},'recording_launcher_sha256':sha(P/'LAUNCH-RECORDED.py'),'largest_file_bytes':largest,'observed_free_bytes':free,'required_free_strictly_above_bytes':11*2**30,'observed_available_memory_bytes':mem,'required_available_memory_bytes':7*2**30,'active_lean_lake_processes':active,'compiler_or_builder_invoked':False,'hash_checked_files':len(memo),'hash_checked_bytes':hashed,'elapsed_seconds':time.monotonic()-start}
(O/'PREFLIGHT-RESULT.json').write_text(json.dumps(result,indent=2)+'\n');(O/'PREFLIGHT-CONTEXT-LEDGER.json').write_text(json.dumps({'native_runtime':current_native,'external_imports':extbindings,'accepted_receipts':receipts},indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['staged_script_pins','staged_config_pins']},indent=2))
