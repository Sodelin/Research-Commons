"""Versioned audit-output-only wrapper around preserved strict connected builder.
Non-audit invocation bodies, graph/cache/native/resource rules stay inherited.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,time,types
ROOT=Path(__file__).resolve().parents[1]
HELPER_SHA='398f7a2fef10fff0b1f50f02e10ce1a1ab860c352f2591fb3a769a1040fe96cd'
def require(x,msg):
 if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p,h,name):
 require(not p.is_symlink(),'wrapper symlink');raw=p.read_bytes();require(hashlib.sha256(raw).hexdigest()==h,'wrapper hash mismatch');m=types.ModuleType(name);m.__file__=str(p);exec(compile(raw,str(p),'exec'),m.__dict__);return m
stream=load(ROOT/'scripts/audit_stream.py',HELPER_SHA,'private_audit_stream')
desktop=load(ROOT/'scripts/build_desktop.py','a9d4d3f210eec5d01152661ca360e12cac295d8fdb1286ce99f548f307daf941','private_preserved_desktop')
core=desktop.auth.original.core
require(sha(ROOT/'scripts/build_connected.py')=='13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc','core drift')
BINARY=core.BINARY;MATHLIB=core.MATHLIB;save=core.save;safe=core.safe;artifact_bundle=core.artifact_bundle;AUDITS={};raw_read=core.read
def read_with_explicit_audit(path):
 p=Path(path);meta=AUDITS.get(str(p))
 if meta is None:return raw_read(p)
 require(not p.exists() and not p.is_symlink(),'unexpected raw audit representation')
 require(meta['raw_path']==str(p),'audit path mismatch')
 return json.loads(stream.read_bytes(meta))
core.read=read_with_explicit_audit
class StreamedAuditBuilder(desktop.DesktopBuilder):
 def __init__(self):
  super().__init__()
  save(self.run/'STREAMED-AUDIT-PINS.json',{'wrapper_sha256':sha(Path(__file__)),'helper_sha256':HELPER_SHA,'preserved_core_sha256':sha(ROOT/'scripts/build_connected.py'),'proof_audit_source_and_assertions_unchanged':True,'output_contract':'audit-only FIFO to exact gzip, raw logical auxiliary with explicit reader','resource_limits_unchanged':True})
  shutil.copyfile(Path(__file__),self.run/'STREAMED-AUDIT-WRAPPER.py');shutil.copyfile(ROOT/'scripts/audit_stream.py',self.run/'AUDIT-STREAM-HELPER.py')
 def invoke(self,name,source,obj,imports,context,seconds,memory,kind):
  if kind!='complete-owned-audit':return super().invoke(name,source,obj,imports,context,seconds,memory,kind)
  return self.invoke_streamed(name,source,obj,imports,context,seconds,memory,kind)
 def invoke_streamed(self,name,source,obj,imports,context,seconds,memory,kind):
  require(kind=='complete-owned-audit' and not obj and name=='OwnedAudit','streaming restricted to audit')
  self.authenticate_inventory(context)
  self.attempt+=1;attempt=self.run/'attempts'/f'{self.attempt:05d}-{safe(name)}';attempt.mkdir(parents=True)
  work=attempt/'work';work.mkdir();(attempt/'evidence').mkdir();frozen=work/(name.replace('.','/')+'.lean');frozen.parent.mkdir(parents=True,exist_ok=True);frozen.write_bytes(source.read_bytes());before=self.dependencies(context,imports);env=dict(os.environ,LEAN_PATH=':'.join(map(str,[context]+self.external)),LEAN_NUM_THREADS='1',LD_DEBUG='libs',LD_DEBUG_OUTPUT=str(attempt/'NATIVE-LOADER'))
  output=attempt/(name.replace('.','/')+'.olean');output.parent.mkdir(parents=True,exist_ok=True);cmd=[str(self.bin/'lean'),'-j1','-t0','-M'+str(memory),'-Ddebug.skipKernelTC=false']
  if obj:cmd+=['-o',str(output)]
  cmd+=[str(frozen.relative_to(work))];start=time.monotonic();code=None
  with (attempt/'stdout').open('wb') as out,(attempt/'stderr').open('wb') as err:
   code,transport=stream.capture(cmd,work,env,out,err,seconds)
  after=self.dependencies(context,imports);native_stable=all([p.stat().st_dev,p.stat().st_ino,p.stat().st_size,p.stat().st_mtime_ns,p.stat().st_ctime_ns]==self.native_runtime[str(p)]['stat_identity'] for p in self.native_paths);loader_files=list(attempt.glob('NATIVE-LOADER.*'));native_used=sorted({str(Path(x).resolve()) for p in loader_files for x in re.findall(r'calling init:\s*(/[^\s]+)',p.read_text(errors='replace'))});native_known=bool(loader_files) and all(p in self.native_runtime for p in native_used);stable=before==after and sha(source)==sha(frozen) and native_stable and native_known
  log=(attempt/'stdout').read_text(errors='replace')+(attempt/'stderr').read_text(errors='replace');passed=code==0 and stable and 'sorryAx' not in log and transport is not None
  rec={'status':'PASS_FRESH_KERNEL_CHECK' if passed else 'FAILED_OR_RESOURCE','module':name,'kind':kind,'source_sha256':sha(frozen),'compiler_sha256':BINARY,'mathlib_commit':MATHLIB,'command':cmd,'cap_seconds':seconds,'cap_memory_mib':memory,'exit_code':code,'elapsed_seconds':time.monotonic()-start,'source_and_imports_stable':stable,'native_runtime_digest':self.native_digest,'native_runtime_stat_stable':native_stable,'native_loader_outputs':[{'path':str(p),'sha256':sha(p)} for p in loader_files],'native_initialized_libraries':{p:self.native_runtime.get(p) for p in native_used},'native_initialized_libraries_bound':native_known,'direct_import_bindings':before,'direct_import_sha256':{m:x['sha256'] for m,x in before.items()},'direct_import_artifacts':{m:x['artifacts'] for m,x in before.items()},'stdout_sha256':sha(attempt/'stdout'),'stderr_sha256':sha(attempt/'stderr'),'receipt_directory':str(attempt)}
  if passed and obj:rec.update(object_sha256=sha(output),object_artifacts=artifact_bundle(output))
  rec['working_directory']=str(work);rec['auxiliary_outputs']=[{'path':str(p.relative_to(attempt)),'sha256':sha(p),'bytes':p.stat().st_size} for p in attempt.rglob('*.json') if p.name!='receipt.json']
  rec['capture_return_code']=code
  rec['compiler_exit_code']=transport['child_exit_code'] if transport is not None else json.loads((work/'AUDIT-STREAM-FAILED.json').read_bytes())['child_exit_code']
  rec['exit_code_semantics']='Invocation status: actual compiler exit is separately recorded;125 denotes capture failure and124 timeout'
  if transport is not None:
   rec['audit_transport']=transport
   rec['auxiliary_outputs'].append({'path':'work/AUDIT-RESULT.json','sha256':transport['raw_sha256'],'bytes':transport['raw_bytes'],'storage':'logical raw audit, exact bytes in receipt-bound gzip; explicit reader required'})
   rec['audit_stream_helper_sha256']=HELPER_SHA
   rec['audit_stream_wrapper_sha256']=sha(Path(__file__))
   AUDITS[str(work/'AUDIT-RESULT.json')]=transport
  save(attempt/'receipt.json',rec)
  self.authenticate_inventory(context)
  if not passed:return rec,None
  if not obj:rec['audit_output']=str(work/'AUDIT-RESULT.json')
  return rec,output if obj else None

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('target');args=ap.parse_args();b=StreamedAuditBuilder();require(args.target in b.graph['targets'],'unknown target');raise SystemExit(b.run_targets([args.target]))
