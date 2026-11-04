#!/usr/bin/env python3
"""Pinned profile-aware integration. Existing sources and receipts are never overwritten."""
from pathlib import Path
import argparse,collections,datetime,fcntl,hashlib,json,os,re,shutil,subprocess,time
ROOT=Path(__file__).resolve().parents[1]
COMPILER='819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
BINARY='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_bytes())
def save(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
def safe(s):return re.sub('[^A-Za-z0-9_-]','_',s)
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir']
def companion(base,suffix):return base.with_suffix(suffix) if suffix in ['.olean','.ilean','.ir'] else Path(str(base)+suffix[len('.olean'):])
def artifact_bundle(base):return {suffix:sha(companion(base,suffix)) for suffix in SUFFIXES if companion(base,suffix).is_file()}

class Builder:
 def __init__(self):
  self.graph=read(ROOT/'DEPENDENCY-GRAPH.json');self.graph_sha=sha(ROOT/'DEPENDENCY-GRAPH.json');self.cache=ROOT/'.build/cache';self.cache.mkdir(parents=True,exist_ok=True)
  self.lock=(ROOT/'.build/lock').open('w');fcntl.flock(self.lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
  self.bin=Path(os.environ['CONNECTED_LEAN_BIN']).resolve();self.mathlib=Path(os.environ['CONNECTED_MATHLIB']).resolve();assert sha(self.bin/'lean')==BINARY
  assert subprocess.check_output(['git','-C',str(self.mathlib),'rev-parse','HEAD'],text=True).strip()==MATHLIB
  self.external=sorted((self.mathlib/'.lake/packages').glob('*/.lake/build/lib/lean'))+[self.mathlib/'.lake/build/lib/lean',self.bin.parent/'lib/lean']
  linked=subprocess.check_output(['ldd',str(self.bin/'lean')],text=True);self.native_paths=sorted({Path(x).resolve() for x in re.findall(r'(/[^\s()]+)',linked) if Path(x).is_file()} | {p.resolve() for p in (self.bin.parent/'lib').rglob('*.so*') if p.is_file()} | {p.resolve() for p in (self.mathlib/'.lake').rglob('*.so*') if p.is_file()});self.native_runtime={str(p):{'sha256':sha(p),'bytes':p.stat().st_size,'stat_identity':[p.stat().st_dev,p.stat().st_ino,p.stat().st_size,p.stat().st_mtime_ns,p.stat().st_ctime_ns]} for p in self.native_paths};self.native_digest=hashlib.sha256(json.dumps({p:v['sha256'] for p,v in self.native_runtime.items()},sort_keys=True).encode()).hexdigest()
  stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');self.run=ROOT/'.build/runs'/stamp;self.run.mkdir(parents=True)
  self.candidates=[] # External prior-object admission is disabled for this fresh integration replay.
  save(self.run/'NATIVE-RUNTIME-PINS.json',{'native_runtime_digest':self.native_digest,'libraries':self.native_runtime,'identity_boundary':'Complete ldd-linked libraries and conservative Lean-distribution/mathlib-package shared-library superset. Per-attempt glibc loader traces identify initialized native libraries.'});save(self.run/'RUNNER-AND-INPUT-PINS.json',{'builder_sha256':sha(Path(__file__)),'audit_template_sha256':sha(ROOT/'scripts/AuditTemplate.lean'),'graph_sha256':self.graph_sha});shutil.copy2(Path(__file__),self.run/'BUILDER.py');shutil.copy2(ROOT/'DEPENDENCY-GRAPH.json',self.run/'DEPENDENCY-GRAPH.json');shutil.copy2(ROOT/'scripts/AuditTemplate.lean',self.run/'AuditTemplate.lean');self.results=[];self.attempt=0;self.failed_keys=set(read(ROOT/'.build/FAILED-KEYS.json')) if (ROOT/'.build/FAILED-KEYS.json').exists() else set();self.events=(self.run/'EVENTS.jsonl').open('a');self.counts=collections.Counter();self.audit_template=(ROOT/'scripts/AuditTemplate.lean').read_text();assert self.audit_template.count('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]')==1,'Audit module-list placeholder must occur exactly once';save(ROOT/'.build/LATEST-RUN.json',{'run':str(self.run),'graph_sha256':self.graph_sha,'status':'RUNNING'})
 def event(self,**d):
  self.events.write(json.dumps(d)+'\n');self.events.flush();print(json.dumps(d),flush=True)
 def dependencies(self,obj,mods):
  d={}
  for m in mods:
   rel=m.replace('.','/')+'.olean';p=next((r/rel for r in [obj]+self.external if (r/rel).is_file()),None)
   if p is None:raise RuntimeError('Missing actual import '+m)
   d[m]={'path':str(p),'sha256':sha(p),'artifacts':artifact_bundle(p)}
  return d
 def install(self,base,out,expected):
  assert artifact_bundle(base)==expected,('Source companion bundle drift',base)
  out.parent.mkdir(parents=True,exist_ok=True)
  for suffix in SUFFIXES:
   p=base.with_suffix(suffix) if suffix in ['.olean','.ilean','.ir'] else Path(str(base) + suffix[len('.olean'):])
   q=out.with_suffix(suffix) if suffix in ['.olean','.ilean','.ir'] else Path(str(out)+suffix[len('.olean'):])
   if p.exists():
    if q.exists():assert sha(q)==sha(p),('Existing context artifact differs',q)
    else:os.link(p,q)
 def cache_result(self,key,rec,obj):
  destination=self.cache/key;folder=self.cache/('.staging-'+key+'-'+str(time.time_ns()));folder.mkdir(exist_ok=False)
  for suffix in SUFFIXES:
   source=obj.with_suffix(suffix) if suffix in ['.olean','.ilean','.ir'] else Path(str(obj)+suffix[len('.olean'):])
   if source.exists():shutil.copy2(source,folder/('artifact'+suffix))
  assert artifact_bundle(folder/'artifact.olean')==rec['object_artifacts']
  rec={**rec,'cached_object':str(destination/'artifact.olean')};save(folder/'receipt.json',rec)
  if destination.exists():
   if (destination/'receipt.json').exists():raise RuntimeError('Completed cache key already exists; refusing overwrite '+key)
   quarantine=self.cache/('.incomplete-'+key+'-'+str(time.time_ns()));destination.rename(quarantine);self.event(cache_key=key,status='INCOMPLETE_CACHE_PRESERVED',path=str(quarantine))
  folder.rename(destination);return rec
 def invoke(self,name,source,obj,imports,context,seconds,memory,kind):
  self.attempt+=1;attempt=self.run/'attempts'/f'{self.attempt:05d}-{safe(name)}';attempt.mkdir(parents=True)
  work=attempt/'work';work.mkdir();(attempt/'evidence').mkdir();frozen=work/(name.replace('.','/')+'.lean');frozen.parent.mkdir(parents=True,exist_ok=True);frozen.write_bytes(source.read_bytes());before=self.dependencies(context,imports);env=dict(os.environ,LEAN_PATH=':'.join(map(str,[context]+self.external)),LEAN_NUM_THREADS='1',LD_DEBUG='libs',LD_DEBUG_OUTPUT=str(attempt/'NATIVE-LOADER'))
  output=attempt/(name.replace('.','/')+'.olean');output.parent.mkdir(parents=True,exist_ok=True);cmd=[str(self.bin/'lean'),'-j1','-t0','-M'+str(memory),'-Ddebug.skipKernelTC=false']
  if obj:cmd+=['-o',str(output)]
  cmd+=[str(frozen.relative_to(work))];start=time.monotonic();code=None
  with (attempt/'stdout').open('wb') as out,(attempt/'stderr').open('wb') as err:
   try:code=subprocess.run(cmd,cwd=work,env=env,stdout=out,stderr=err,timeout=seconds).returncode
   except subprocess.TimeoutExpired:code=124
  after=self.dependencies(context,imports);native_stable=all([p.stat().st_dev,p.stat().st_ino,p.stat().st_size,p.stat().st_mtime_ns,p.stat().st_ctime_ns]==self.native_runtime[str(p)]['stat_identity'] for p in self.native_paths);loader_files=list(attempt.glob('NATIVE-LOADER.*'));native_used=sorted({str(Path(x).resolve()) for p in loader_files for x in re.findall(r'calling init:\s*(/[^\s]+)',p.read_text(errors='replace'))});native_known=bool(loader_files) and all(p in self.native_runtime for p in native_used);stable=before==after and sha(source)==sha(frozen) and native_stable and native_known
  log=(attempt/'stdout').read_text(errors='replace')+(attempt/'stderr').read_text(errors='replace');passed=code==0 and stable and 'sorryAx' not in log
  rec={'status':'PASS_FRESH_KERNEL_CHECK' if passed else 'FAILED_OR_RESOURCE','module':name,'kind':kind,'source_sha256':sha(frozen),'compiler_sha256':BINARY,'mathlib_commit':MATHLIB,'command':cmd,'cap_seconds':seconds,'cap_memory_mib':memory,'exit_code':code,'elapsed_seconds':time.monotonic()-start,'source_and_imports_stable':stable,'native_runtime_digest':self.native_digest,'native_runtime_stat_stable':native_stable,'native_loader_outputs':[{'path':str(p),'sha256':sha(p)} for p in loader_files],'native_initialized_libraries':{p:self.native_runtime.get(p) for p in native_used},'native_initialized_libraries_bound':native_known,'direct_import_bindings':before,'direct_import_sha256':{m:x['sha256'] for m,x in before.items()},'direct_import_artifacts':{m:x['artifacts'] for m,x in before.items()},'stdout_sha256':sha(attempt/'stdout'),'stderr_sha256':sha(attempt/'stderr'),'receipt_directory':str(attempt)}
  if passed and obj:rec.update(object_sha256=sha(output),object_artifacts=artifact_bundle(output))
  rec['working_directory']=str(work);rec['auxiliary_outputs']=[{'path':str(p.relative_to(attempt)),'sha256':sha(p),'bytes':p.stat().st_size} for p in attempt.rglob('*.json') if p.name!='receipt.json'];save(attempt/'receipt.json',rec)
  if not passed:return rec,None
  if not obj:rec['audit_output']=str(work/'AUDIT-RESULT.json')
  return rec,output if obj else None
 def component(self,m,e,context):
  source=ROOT/'source-store'/(e['sha256']+'.lean');assert sha(source)==e['sha256'];before=self.dependencies(context,e['imports']);deps={n:x['sha256'] for n,x in before.items()};bundles={n:x['artifacts'] for n,x in before.items()};key_data={'module':m,'source':e['sha256'],'compiler':BINARY,'mathlib':MATHLIB,'trust':0,'kernel_check':True,'imports':bundles,'native_runtime_digest':self.native_digest,'artifact_boundary':'olean-private-server-ilean-ir-native-v3'};theta_exception=m=='ThetaCertificate5' and e['sha256']=='e541af41b215cf473e63d4e968fdc42b31fe74f6384387f66de61f1ebbd7fbab';key_data.update({'resource_exception':{'memory_mib':6144,'seconds':600}} if theta_exception else {});key=hashlib.sha256(json.dumps(key_data,sort_keys=True).encode()).hexdigest();dest=context/(m.replace('.','/')+'.olean');cached=self.cache/key/'receipt.json'
  if key in self.failed_keys:raise RuntimeError('Previously failed exact component key '+m)
  if cached.exists():
   rec=read(cached);p=Path(rec['cached_object']);assert rec['source_sha256']==e['sha256'] and rec['direct_import_artifacts']==bundles and artifact_bundle(p)==rec['object_artifacts'];self.install(p,dest,rec['object_artifacts']);self.counts['cache_reuse']+=1;return rec
  for cand in self.candidates:
   if cand['module']==m and cand['source_sha256']==e['sha256'] and cand['compiler_sha256']==BINARY and cand.get('direct_import_artifacts')==bundles:
    p=Path(cand['object_path']);assert artifact_bundle(p)==cand['object_artifacts'];rec=self.cache_result(key,{**cand,'status':'PASS_REUSED_AUTHENTICATED_PRIOR','direct_import_sha256':deps},p);self.install(Path(rec['cached_object']),dest,rec['object_artifacts']);self.counts['prior_reuse']+=1;self.event(component=m,status='REUSED_PRIOR');return rec
  seconds,memory=(600,6144) if theta_exception else (180,4096)
  if theta_exception:
   available_kib=int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))
   if available_kib<7168*1024:raise RuntimeError('ThetaCertificate5 exception waits for at least 7168MiB available memory; measured '+str(available_kib//1024)+'MiB')
   self.event(component=m,status='APPROVED_HISTORICAL_MEMORY_EXCEPTION',cap_memory_mib=6144,cap_seconds=600,available_memory_mib=available_kib//1024)
  rec,obj=self.invoke(m,source,True,e['imports'],context,seconds,memory,'component')
  if not obj:self.failed_keys.add(key);save(ROOT/'.build/FAILED-KEYS.json',sorted(self.failed_keys));self.event(component=m,status=rec['status'],seconds=rec['elapsed_seconds']);raise RuntimeError('Component failed '+m)
  rec=self.cache_result(key,rec,obj);self.install(Path(rec['cached_object']),dest,rec['object_artifacts']);self.counts['fresh_components']+=1;self.event(component=m,status='FRESH_KERNEL_PASS',seconds=round(rec['elapsed_seconds'],3));return rec
 def target(self,label):
  g=self.graph['targets'][label];r=self.run/'targets'/safe(label);r.mkdir(parents=True);context=r/'objects';context.mkdir();start=time.monotonic();records=[]
  try:
   for m in g['order']:records.append(self.component(m,g['modules'][m],context))
   name='Connected_'+safe(label);src=r/(name+'.lean');src.write_text('\n'.join('import '+m for m in g['roots'])+'\n');combined=label=='connected/compatible';seconds,memory=(300,4096) if combined else (180,4096);rec,obj=self.invoke(name,src,True,g['roots'],context,seconds,memory,'aggregate');
   if not obj:raise RuntimeError('Aggregate failed '+label)
   self.install(obj,context/(name+'.olean'),rec['object_artifacts']);audit=r/'OwnedAudit.lean';body=self.audit_template.replace('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]','#'+json.dumps(g['order'])).replace('"AUDIT-OWNED.json"','"AUDIT-RESULT.json"');audit.write_text('\n'.join('import '+m for m in g['roots'])+'\n'+body);ar,_=self.invoke('OwnedAudit',audit,False,g['roots']+['Lean.Util.CollectAxioms'],context,seconds,memory,'complete-owned-audit')
   if ar['exit_code']!=0:raise RuntimeError('Audit failed '+label)
   a=read(Path(ar['audit_output']));assert a['selected_modules']==g['order'],'Audit selected module list differs from intended complete closure';assert not a['owned_axioms'] and not a['nonstandard_axiom_rows'] and not a['missing_modules']
   artifacts=[]
   for module in a['all_imported_module_names']:
    item=self.dependencies(context,[module])[module];op=Path(item['path'])
    for suffix in SUFFIXES:
     ap=op.with_suffix(suffix) if suffix in ['.olean','.ilean','.ir'] else Path(str(op)+suffix[len('.olean'):])
     if ap.exists():artifacts.append({'module':module,'suffix':suffix,'path':str(ap),'bytes':ap.stat().st_size,'sha256':sha(ap)})
   save(r/'ACTUAL-IMPORTED-ARTIFACTS.json',artifacts)
   result={'target':label,'status':'PASS','roots':len(g['roots']),'closure_modules':len(g['modules']),'declarations':a['declaration_count'],'theorems':a['theorem_declaration_count'],'aggregate_receipt':rec,'audit_receipt':ar,'component_receipts':records,'seconds':time.monotonic()-start}
  except Exception as ex:result={'target':label,'status':'FAILED_OR_BLOCKED','error':str(ex),'component_receipts':records,'seconds':time.monotonic()-start}
  save(r/'RESULT.json',result);self.results.append(result);save(self.run/'TARGET-SUMMARY.json',[{k:v for k,v in x.items() if k not in ['component_receipts','aggregate_receipt','audit_receipt']} for x in self.results]);self.event(target=label,status=result['status'],seconds=round(result['seconds'],3));return result
 def run_targets(self,labels):
  for label in labels:self.target(label)
  native_final={str(p):sha(p) for p in self.native_paths};native_final_stable=all(native_final[p]==v['sha256'] for p,v in self.native_runtime.items());save(self.run/'NATIVE-RUNTIME-FINAL-REHASH.json',{'stable':native_final_stable,'hashes':native_final});ok=all(r['status']=='PASS' for r in self.results) and native_final_stable;rec={'status':'PASS_ALL_REQUESTED_TARGETS' if ok else 'INCOMPLETE_TARGET_FAILURES_PRESERVED','graph_sha256':self.graph_sha,'native_runtime_digest':self.native_digest,'native_runtime_final_rehash_stable':native_final_stable,'compiler_sha256':BINARY,'mathlib_commit':MATHLIB,'targets_requested':labels,'targets_passed':[r['target'] for r in self.results if r['status']=='PASS'],'counts':dict(self.counts),'run':str(self.run),'new_mathematical_theorem_claimed':False,'fresh_all_sources_claimed':False,'fresh_every_selected_component_context_in_this_run':all(str(c.get('receipt_directory','')).startswith(str(self.run)+'/attempts/') for r in self.results for c in r['component_receipts']) and ok,'freshness_note':'Explicit counts and each component receipt directory establish current-run compilation versus authenticated exact-context reuse. Never infer freshness from successful aggregates or absence of prior candidate reuse.','trust_level':0,'kernel_checking':True,'ordinary_memory_cap_mib':4096,'single_exact_source_memory_exception':{'module':'ThetaCertificate5','sha256':'e541af41b215cf473e63d4e968fdc42b31fe74f6384387f66de61f1ebbd7fbab','memory_mib':6144,'seconds':600},'component_count_semantics':'Successful exact artifact-context cache admissions and reuse events; unique source and context identities remain in the component receipts'};save(self.run/'FINAL-RECEIPT.json',rec);save(ROOT/'.build/LATEST-RUN.json',rec);return 0 if ok else 1
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('target',nargs='?',default='accepted');args=ap.parse_args();b=Builder();labels=list(b.graph['targets']) if args.target=='all' else [k for k,v in b.graph['targets'].items() if v.get('required_for_accepted_release',True)] if args.target=='accepted' else [k for k,v in b.graph['targets'].items() if not v.get('required_for_accepted_release',True)] if args.target=='provisional' else [args.target];raise SystemExit(b.run_targets(labels))
