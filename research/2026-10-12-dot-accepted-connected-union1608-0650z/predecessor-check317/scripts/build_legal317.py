"""Separate exact317 target: no prerequisite compiler fallback; streamed audit retained."""
from pathlib import Path
import hashlib,json,sys,types,shutil
ROOT=Path(__file__).resolve().parents[1]
TARGET='candidate/g4-legal-panel-comb'
GRAPH_SHA='b11bd77adcd63c0416fb327419fb5eadbf4457cbe3fd444032ef5a04ab1a6e09'
STREAMED_SHA='748ea65d03736c89f6f868e431e00cdc9e21937273c227e9b5cc5c16a1e37ea1'
FRESH={'G4ActualLegalPanelComb': '4fd78fc530e103512f4dc98a7e60ac2d592ad666e7feac17b5ab1456f1a961c9'}
def require(x,msg):
 if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def allowed_invocation(name,source_sha,obj,seconds,memory,kind):
 if (seconds,memory)!=(180,4096):return False
 if kind=='component':return bool(obj) and FRESH.get(name)==source_sha
 if kind=='aggregate':return bool(obj) and name=='Connected_candidate_g4-legal-panel-comb'
 if kind=='complete-owned-audit':return not obj and name=='OwnedAudit'
 return False
def load(p,digest):
 require(not p.is_symlink(),'wrapper symlink')
 raw=p.read_bytes();require(hashlib.sha256(raw).hexdigest()==digest,'streamed wrapper drift')
 m=types.ModuleType('private_exact_narrow_streamed');m.__file__=str(p)
 exec(compile(raw,str(p),'exec'),m.__dict__);return m
require(sha(ROOT/'DEPENDENCY-GRAPH.json')==GRAPH_SHA,'exact narrow graph required')
graph=json.loads((ROOT/'DEPENDENCY-GRAPH.json').read_bytes())
require(set(graph['targets'])=={TARGET},'only exact narrow target permitted')
mods=graph['targets'][TARGET]['modules']
require(len(mods)==317 and not any(m.startswith('Mathlib.') for m in mods),'empty owned Mathlib317 graph required')
for name,digest in FRESH.items():require(mods[name]['sha256']==digest,'fresh source identity drift')
streamed=load(ROOT/'scripts/build_streamed_audit.py',STREAMED_SHA)
require(len(streamed.desktop.auth.original.OWNED_MATHLIB)==4,'unexpected inherited namespace specialization')
streamed.desktop.auth.original.OWNED_MATHLIB={}
class NarrowBuilder(streamed.StreamedAuditBuilder):
 def __init__(self):
  super().__init__();self.narrow_invocations=0
  streamed.save(self.run/'LEGAL317-PINS.json',{'wrapper_sha256':sha(Path(__file__)),'graph_sha256':GRAPH_SHA,'target':TARGET,'fresh_component_allowlist':FRESH,'prerequisite_compile_fallback':'REJECTED_BEFORE_INVOCATION','owned_mathlib_modules':[],'full_official_namespace_retained':True,'max_fresh_invocations':3,'inherited_streamed_wrapper_sha256':STREAMED_SHA,'compiler_memory_time_kernel_import_native_audit_checks_unchanged':True})
  shutil.copyfile(Path(__file__),self.run/'LEGAL317-WRAPPER.py')
 def invoke(self,name,source,obj,imports,context,seconds,memory,kind):
  require(allowed_invocation(name,sha(source),obj,seconds,memory,kind),'Narrow target refuses prerequisite rebuild or unapproved invocation: '+name)
  require(self.narrow_invocations<3,'narrow invocation count exceeded')
  self.narrow_invocations+=1
  return super().invoke(name,source,obj,imports,context,seconds,memory,kind)
if __name__=='__main__':
 require(len(sys.argv)==2 and sys.argv[1]==TARGET,'explicit exact narrow target required')
 builder=NarrowBuilder();raise SystemExit(builder.run_targets([TARGET]))
