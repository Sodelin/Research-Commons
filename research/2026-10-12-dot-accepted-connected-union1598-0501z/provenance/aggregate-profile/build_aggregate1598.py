"""Exact1598 aggregate-only target: all component compiler fallback rejected."""
from pathlib import Path
import hashlib,json,sys,types,shutil
ROOT=Path(__file__).resolve().parents[1]
TARGET='current/connected'
GRAPH_SHA='9a8467c792c066cc97b939c05ddef04a77bdf21447fcb2df832be84215ec253e'
STREAMED_SHA='748ea65d03736c89f6f868e431e00cdc9e21937273c227e9b5cc5c16a1e37ea1'
def require(x,msg):
 if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def allowed_invocation(name,source_sha,obj,seconds,memory,kind):
 if (seconds,memory)!=(300,6144):return False
 if kind=='aggregate':return bool(obj) and name=='Connected_current_connected'
 if kind=='complete-owned-audit':return not obj and name=='OwnedAudit'
 return False

def load(p,digest):
 require(not p.is_symlink(),'wrapper symlink')
 raw=p.read_bytes();require(hashlib.sha256(raw).hexdigest()==digest,'streamed wrapper drift')
 m=types.ModuleType('private_exact_narrow_streamed');m.__file__=str(p)
 exec(compile(raw,str(p),'exec'),m.__dict__);return m
require(sha(ROOT/'DEPENDENCY-GRAPH.json')==GRAPH_SHA,'exact1598 graph required')
graph=json.loads((ROOT/'DEPENDENCY-GRAPH.json').read_bytes())
require(TARGET in graph['targets'],'exact current target required')
mods=graph['targets'][TARGET]['modules']
require(len(mods)==1598,'exact1598 graph required')
streamed=load(ROOT/'scripts/build_streamed_audit.py',STREAMED_SHA)
require(len(streamed.desktop.auth.original.OWNED_MATHLIB)==4,'full four-owned namespace required')
class AggregateOnlyBuilder(streamed.StreamedAuditBuilder):
 def __init__(self):
  super().__init__();self.narrow_invocations=0
  streamed.save(self.run/'AGGREGATE1598-PINS.json',{'wrapper_sha256':sha(Path(__file__)),'graph_sha256':GRAPH_SHA,'target':TARGET,'fresh_component_allowlist':{},'prerequisite_compile_fallback':'REJECTED_BEFORE_INVOCATION','owned_mathlib_modules':sorted(streamed.desktop.auth.original.OWNED_MATHLIB),'accepted_four_owned_namespace_retained':True,'max_fresh_invocations':2,'inherited_streamed_wrapper_sha256':STREAMED_SHA,'compiler_memory_time_kernel_import_native_audit_checks_unchanged':True})
  shutil.copyfile(Path(__file__),self.run/'AGGREGATE1598-WRAPPER.py')
 def invoke(self,name,source,obj,imports,context,seconds,memory,kind):
  require(allowed_invocation(name,sha(source),obj,seconds,memory,kind),'Aggregate-only target refuses prerequisite rebuild or unapproved invocation: '+name)
  require(self.narrow_invocations<2,'aggregate-only invocation count exceeded')
  self.narrow_invocations+=1
  return super().invoke(name,source,obj,imports,context,seconds,memory,kind)
if __name__=='__main__':
 require(len(sys.argv)==2 and sys.argv[1]==TARGET,'explicit exact full aggregate target required')
 builder=AggregateOnlyBuilder();raise SystemExit(builder.run_targets([TARGET]))
