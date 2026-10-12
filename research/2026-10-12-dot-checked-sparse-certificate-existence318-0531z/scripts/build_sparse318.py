"""Separate exact318 target: no prerequisite compiler fallback; streamed audit retained."""
from pathlib import Path
import hashlib,json,sys,types,shutil
ROOT=Path(__file__).resolve().parents[1]
TARGET='candidate/g4-sparse-certificate-existence'
GRAPH_SHA='ae13a9ff03f834633a33ec1d8d0a6f6ec497b9119075fdf6ff932b5c9e1a0714'
STREAMED_SHA='748ea65d03736c89f6f868e431e00cdc9e21937273c227e9b5cc5c16a1e37ea1'
FRESH={'G4ActualSparseCertificateExistence': '9ea04cbe390030381624d25b20be10751dff62f75d5d6e7752b88b9599a46418', 'Mathlib.Algebra.Polynomial.RuleOfSigns': '7e8c440db1d4d9ecdeb248f2caac59cbd71351f10f1ffdd82d66daebcfe84b3e', 'Mathlib.Algebra.Polynomial.CoeffList': '98bacb29fe3175fbb3f17544b09c1bf1324871d12bee6551638c5e42e713b269', 'Mathlib.Data.List.Destutter': 'adaa2255e20191805154bda8e146bc419cbd4550f36fb5f63dfee289f9342134', 'Mathlib.Algebra.Polynomial.Basis': '75b326d7f4d3216da9e58dce0bd38d97bd55c41ab016e6deafd74eb82e7bca8d', 'Mathlib.Analysis.Polynomial.Order': 'bf05560594215319b7288b07403bd818d378f6f8e2ea59da58d31cde31ae6d27', 'Mathlib.Analysis.Polynomial.Basic': '6cd16c6cc5450af245e00c691f20dd2a63f072f54ad0361e0c3fea3a08b76d00', 'Mathlib.Analysis.Asymptotics.SpecificAsymptotics': '1e238d248bacb49378e0961d34e99f4ba9a876498ceaed7ce27e654a4334b738'}
OWNED={'Mathlib.Algebra.Polynomial.RuleOfSigns': '7e8c440db1d4d9ecdeb248f2caac59cbd71351f10f1ffdd82d66daebcfe84b3e', 'Mathlib.Algebra.Polynomial.CoeffList': '98bacb29fe3175fbb3f17544b09c1bf1324871d12bee6551638c5e42e713b269', 'Mathlib.Data.List.Destutter': 'adaa2255e20191805154bda8e146bc419cbd4550f36fb5f63dfee289f9342134', 'Mathlib.Algebra.Polynomial.Basis': '75b326d7f4d3216da9e58dce0bd38d97bd55c41ab016e6deafd74eb82e7bca8d', 'Mathlib.Analysis.Polynomial.Order': 'bf05560594215319b7288b07403bd818d378f6f8e2ea59da58d31cde31ae6d27', 'Mathlib.Analysis.Polynomial.Basic': '6cd16c6cc5450af245e00c691f20dd2a63f072f54ad0361e0c3fea3a08b76d00', 'Mathlib.Analysis.Asymptotics.SpecificAsymptotics': '1e238d248bacb49378e0961d34e99f4ba9a876498ceaed7ce27e654a4334b738'}
def require(x,msg):
 if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def allowed_invocation(name,source_sha,obj,seconds,memory,kind):
 if (seconds,memory)!=(180,4096):return False
 if kind=='component':return bool(obj) and FRESH.get(name)==source_sha
 if kind=='aggregate':return bool(obj) and name=='Connected_candidate_g4-sparse-certificate-existence'
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
require(len(mods)==318 and {m:e['sha256'] for m,e in mods.items() if m.startswith('Mathlib.')}==OWNED,'exact seven owned upstream Mathlib dependencies required')
for name,digest in FRESH.items():require(mods[name]['sha256']==digest,'fresh source identity drift')
streamed=load(ROOT/'scripts/build_streamed_audit.py',STREAMED_SHA)
require(len(streamed.desktop.auth.original.OWNED_MATHLIB)==4,'unexpected inherited namespace specialization')
streamed.desktop.auth.original.OWNED_MATHLIB=OWNED
class NarrowBuilder(streamed.StreamedAuditBuilder):
 def __init__(self):
  super().__init__();self.narrow_invocations=0
  streamed.save(self.run/'SPARSE318-PINS.json',{'wrapper_sha256':sha(Path(__file__)),'graph_sha256':GRAPH_SHA,'target':TARGET,'fresh_component_allowlist':FRESH,'prerequisite_compile_fallback':'REJECTED_BEFORE_INVOCATION','owned_mathlib_modules':OWNED,'full_official_namespace_retained':True,'max_fresh_invocations':10,'inherited_streamed_wrapper_sha256':STREAMED_SHA,'compiler_memory_time_kernel_import_native_audit_checks_unchanged':True})
  shutil.copyfile(Path(__file__),self.run/'SPARSE318-WRAPPER.py')
 def invoke(self,name,source,obj,imports,context,seconds,memory,kind):
  require(allowed_invocation(name,sha(source),obj,seconds,memory,kind),'Narrow target refuses prerequisite rebuild or unapproved invocation: '+name)
  require(self.narrow_invocations<10,'narrow invocation count exceeded')
  self.narrow_invocations+=1
  return super().invoke(name,source,obj,imports,context,seconds,memory,kind)
if __name__=='__main__':
 require(len(sys.argv)==2 and sys.argv[1]==TARGET,'explicit exact narrow target required')
 builder=NarrowBuilder();raise SystemExit(builder.run_targets([TARGET]))
