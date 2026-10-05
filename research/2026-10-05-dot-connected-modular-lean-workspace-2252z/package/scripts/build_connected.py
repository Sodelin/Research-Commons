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
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean']
def companion(base,suffix):return base.with_suffix(suffix) if suffix in ['.olean','.ilean'] else Path(str(base)+suffix[len('.olean'):])
def artifact_bundle(base):return {suffix:sha(companion(base,suffix)) for suffix in SUFFIXES if companion(base,suffix).is_file()}

class Builder:
 def __init__(self):
  self.graph=read(ROOT/'DEPENDENCY-GRAPH.json');self.graph_sha=sha(ROOT/'DEPENDENCY-GRAPH.json');self.cache=ROOT/'.build/cache';self.cache.mkdir(parents=True,exist_ok=True)
  self.lock=(ROOT/'.build/lock').open('w');fcntl.flock(self.lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
  self.bin=Path(os.environ['CONNECTED_LEAN_BIN']).resolve();self.mathlib=Path(os.environ['CONNECTED_MATHLIB']).resolve();assert sha(self.bin/'lean')==BINARY
  assert subprocess.check_output(['git','-C',str(self.mathlib),'rev-parse','HEAD'],text=True).strip()==MATHLIB
  self.external=sorted((self.mathlib/'.lake/packages').glob('*/.lake/build/lib/lean'))+[self.mathlib/'.lake/build/lib/lean',self.bin.parent/'lib/lean']
  stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');self.run=ROOT/'.build/runs'/stamp;self.run.mkdir(parents=True)
  self.candidates=read(ROOT/'REUSABLE-OBJECT-CANDIDATES.json') if (ROOT/'REUSABLE-OBJECT-CANDIDATES.json').exists() else []
  self.results=[];self.attempt=0;self.failed_keys=set(read(ROOT/'.build/FAILED-KEYS.json')) if (ROOT/'.build/FAILED-KEYS.json').exists() else set();self.events=(self.run/'EVENTS.jsonl').open('a');self.counts=collections.Counter();self.audit_template=(ROOT/'scripts/AuditTemplate.lean').read_text();save(ROOT/'.build/LATEST-RUN.json',{'run':str(self.run),'graph_sha256':self.graph_sha,'status':'RUNNING'})
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
  for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
   p=base.with_suffix(suffix) if suffix in ['.olean','.ilean'] else Path(str(base) + suffix[len('.olean'):])
   q=out.with_suffix(suffix) if suffix in ['.olean','.ilean'] else Path(str(out)+suffix[len('.olean'):])
   if p.exists():
    if q.exists():assert sha(q)==sha(p),('Existing context artifact differs',q)
    else:os.link(p,q)
 def cache_result(self,key,rec,obj):
  folder=self.cache/key;folder.mkdir(exist_ok=False)
  for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
   source=obj.with_suffix(suffix) if suffix in ['.olean','.ilean'] else Path(str(obj)+suffix[len('.olean'):])
   if source.exists():shutil.copy2(source,folder/('artifact'+suffix))
  assert artifact_bundle(folder/'artifact.olean')==rec['object_artifacts']
  rec={**rec,'cached_object':str(folder/'artifact.olean')};save(folder/'receipt.json',rec);return rec
 def invoke(self,name,source,obj,imports,context,seconds,memory,kind):
  self.attempt+=1;attempt=self.run/'attempts'/f'{self.attempt:05d}-{safe(name)}';attempt.mkdir(parents=True)
  frozen=attempt/(name.replace('.','/')+'.lean');frozen.parent.mkdir(parents=True,exist_ok=True);frozen.write_bytes(source.read_bytes());before=self.dependencies(context,imports);env=dict(os.environ,LEAN_PATH=':'.join(map(str,[context]+self.external)),LEAN_NUM_THREADS='1')
  output=attempt/(name.replace('.','/')+'.olean');cmd=[str(self.bin/'lean'),'-j1','-M'+str(memory),'-Ddebug.skipKernelTC=false']
  if obj:cmd+=['-o',str(output)]
  cmd+=[str(frozen.relative_to(attempt))];start=time.monotonic();code=None
  with (attempt/'stdout').open('wb') as out,(attempt/'stderr').open('wb') as err:
   try:code=subprocess.run(cmd,cwd=attempt,env=env,stdout=out,stderr=err,timeout=seconds).returncode
   except subprocess.TimeoutExpired:code=124
  after=self.dependencies(context,imports);stable=before==after and sha(source)==sha(frozen)
  log=(attempt/'stdout').read_text(errors='replace')+(attempt/'stderr').read_text(errors='replace');passed=code==0 and stable and 'sorryAx' not in log
  rec={'status':'PASS_FRESH_KERNEL_CHECK' if passed else 'FAILED_OR_RESOURCE','module':name,'kind':kind,'source_sha256':sha(frozen),'compiler_sha256':BINARY,'mathlib_commit':MATHLIB,'command':cmd,'cap_seconds':seconds,'cap_memory_mib':memory,'exit_code':code,'elapsed_seconds':time.monotonic()-start,'source_and_imports_stable':stable,'direct_import_bindings':before,'direct_import_sha256':{m:x['sha256'] for m,x in before.items()},'direct_import_artifacts':{m:x['artifacts'] for m,x in before.items()},'stdout_sha256':sha(attempt/'stdout'),'stderr_sha256':sha(attempt/'stderr'),'receipt_directory':str(attempt)}
  if passed and obj:rec.update(object_sha256=sha(output),object_artifacts=artifact_bundle(output))
  save(attempt/'receipt.json',rec)
  if not passed:return rec,None
  if not obj:rec['audit_output']=str(attempt/'AUDIT-RESULT.json')
  return rec,output if obj else None
 def component(self,m,e,context):
  source=ROOT/'source-store'/(e['sha256']+'.lean');assert sha(source)==e['sha256'];before=self.dependencies(context,e['imports']);deps={n:x['sha256'] for n,x in before.items()};bundles={n:x['artifacts'] for n,x in before.items()};key=hashlib.sha256(json.dumps({'module':m,'source':e['sha256'],'compiler':BINARY,'mathlib':MATHLIB,'imports':bundles},sort_keys=True).encode()).hexdigest();dest=context/(m.replace('.','/')+'.olean');cached=self.cache/key/'receipt.json'
  if key in self.failed_keys:raise RuntimeError('Previously failed exact component key '+m)
  if cached.exists():
   rec=read(cached);p=Path(rec['cached_object']);assert rec['source_sha256']==e['sha256'] and rec['direct_import_artifacts']==bundles and artifact_bundle(p)==rec['object_artifacts'];self.install(p,dest,rec['object_artifacts']);self.counts['cache_reuse']+=1;return rec
  for cand in self.candidates:
   if cand['module']==m and cand['source_sha256']==e['sha256'] and cand['compiler_sha256']==BINARY and cand.get('direct_import_artifacts')==bundles:
    p=Path(cand['object_path']);assert artifact_bundle(p)==cand['object_artifacts'];rec=self.cache_result(key,{**cand,'status':'PASS_REUSED_AUTHENTICATED_PRIOR','direct_import_sha256':deps},p);self.install(Path(rec['cached_object']),dest,rec['object_artifacts']);self.counts['prior_reuse']+=1;self.event(component=m,status='REUSED_PRIOR');return rec
  seconds,memory=(600,6144) if m=='ThetaCertificate5' else (180,4096);rec,obj=self.invoke(m,source,True,e['imports'],context,seconds,memory,'component')
  if not obj:self.failed_keys.add(key);save(ROOT/'.build/FAILED-KEYS.json',sorted(self.failed_keys));self.event(component=m,status=rec['status'],seconds=rec['elapsed_seconds']);raise RuntimeError('Component failed '+m)
  rec=self.cache_result(key,rec,obj);self.install(Path(rec['cached_object']),dest,rec['object_artifacts']);self.counts['fresh_components']+=1;self.event(component=m,status='FRESH_KERNEL_PASS',seconds=round(rec['elapsed_seconds'],3));return rec
 def target(self,label):
  g=self.graph['targets'][label];r=self.run/'targets'/safe(label);r.mkdir(parents=True);context=r/'objects';context.mkdir();start=time.monotonic();records=[]
  try:
   for m in g['order']:records.append(self.component(m,g['modules'][m],context))
   name='Connected_'+safe(label);src=r/(name+'.lean');src.write_text('\n'.join('import '+m for m in g['roots'])+'\n');combined=label=='connected/compatible';seconds,memory=(300,6144) if combined else (180,4096);rec,obj=self.invoke(name,src,True,g['roots'],context,seconds,memory,'aggregate');
   if not obj:raise RuntimeError('Aggregate failed '+label)
   self.install(obj,context/(name+'.olean'),rec['object_artifacts']);audit=r/'OwnedAudit.lean';body=self.audit_template.replace('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]','#'+json.dumps(g['roots'])).replace('"AUDIT-OWNED.json"','"AUDIT-RESULT.json"');audit.write_text('\n'.join('import '+m for m in g['roots'])+'\n'+body);ar,_=self.invoke('OwnedAudit',audit,False,g['roots']+['Lean.Util.CollectAxioms'],context,seconds,memory,'complete-owned-audit')
   if ar['exit_code']!=0:raise RuntimeError('Audit failed '+label)
   a=read(Path(ar['audit_output']));assert not a['owned_axioms'] and not a['nonstandard_axiom_rows'] and not a['missing_modules']
   artifacts=[]
   for module in a['all_imported_module_names']:
    item=self.dependencies(context,[module])[module];op=Path(item['path'])
    for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
     ap=op.with_suffix(suffix) if suffix in ['.olean','.ilean'] else Path(str(op)+suffix[len('.olean'):])
     if ap.exists():artifacts.append({'module':module,'suffix':suffix,'path':str(ap),'bytes':ap.stat().st_size,'sha256':sha(ap)})
   save(r/'ACTUAL-IMPORTED-ARTIFACTS.json',artifacts)
   result={'target':label,'status':'PASS','roots':len(g['roots']),'closure_modules':len(g['modules']),'declarations':a['declaration_count'],'theorems':a['theorem_declaration_count'],'aggregate_receipt':rec,'audit_receipt':ar,'component_receipts':records,'seconds':time.monotonic()-start}
  except Exception as ex:result={'target':label,'status':'FAILED_OR_BLOCKED','error':str(ex),'component_receipts':records,'seconds':time.monotonic()-start}
  save(r/'RESULT.json',result);self.results.append(result);save(self.run/'TARGET-SUMMARY.json',[{k:v for k,v in x.items() if k not in ['component_receipts','aggregate_receipt','audit_receipt']} for x in self.results]);self.event(target=label,status=result['status'],seconds=round(result['seconds'],3));return result
 def run_targets(self,labels):
  for label in labels:self.target(label)
  ok=all(r['status']=='PASS' for r in self.results);rec={'status':'PASS_ALL_REQUESTED_TARGETS' if ok else 'INCOMPLETE_TARGET_FAILURES_PRESERVED','graph_sha256':self.graph_sha,'compiler_sha256':BINARY,'mathlib_commit':MATHLIB,'targets_requested':labels,'targets_passed':[r['target'] for r in self.results if r['status']=='PASS'],'counts':dict(self.counts),'run':str(self.run),'new_mathematical_theorem_claimed':False,'fresh_all_sources_claimed':False,'component_count_semantics':'Successful exact artifact-context cache admissions and reuse events; unique source and context identities remain in the component receipts'};save(self.run/'FINAL-RECEIPT.json',rec);save(ROOT/'.build/LATEST-RUN.json',rec);return 0 if ok else 1
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('target',nargs='?',default='all');args=ap.parse_args();b=Builder();labels=list(b.graph['targets']) if args.target=='all' else [args.target];raise SystemExit(b.run_targets(labels))
