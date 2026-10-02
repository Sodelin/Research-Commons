#!/usr/bin/env python3
"""Audit every declaration attributed to an immutable selected Lake snapshot."""
from pathlib import Path
import json,hashlib,os,subprocess,time,fcntl,sys,collections
from toolchain import binary_dir
ROOT=Path(__file__).resolve().parents[1]
version=sys.argv[1] if len(sys.argv)>1 else '169-baseline'
SNAPSHOT=ROOT/'snapshots'/version
freeze=json.loads((SNAPSHOT/'FREEZE.json').read_text())
modules=sorted(freeze['artifact_sha256'])
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def stable():
 return all(h(SNAPSHOT/p)==v for p,v in freeze['source_and_config_sha256'].items()) and all(h(SNAPSHOT/'objects'/Path(*m.split('.')).with_suffix('.olean'))==v for m,v in freeze['artifact_sha256'].items())
paths=[SNAPSHOT/'objects',ROOT/'deps/mathlib/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (ROOT/'.lake/packages').iterdir() if p.is_dir()]
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,paths));tool=binary_dir()
with (ROOT/'.build.lock').open('a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 assert stable(),'Frozen snapshot hash mismatch'
 stamp=str(time.time_ns());out=ROOT/'receipts'/('all-declarations-'+version+'-'+stamp);out.mkdir()
 report=out/'declarations.json';progress=out/'progress.txt';source=out/'audit.lean'
 body=(ROOT/'checks/AllDeclarationsTemplate.body').read_text()
 source.write_text('import UnifiedLean\nimport Lean.Util.CollectAxioms\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let selected : Array String := #['+','.join(json.dumps(m) for m in modules)+']\n  let reportFile : String := '+json.dumps(str(report.relative_to(ROOT)))+'\n  let progressFile : String := '+json.dumps(str(progress.relative_to(ROOT)))+'\n'+body)
 command=['timeout',sys.argv[2] if len(sys.argv)>2 else '120',str(tool/'lean'),'-j1','-M4096',str(source)]
 source_hash=h(source);start=time.monotonic()
 with (out/'build.log').open('w') as log:r=subprocess.run(command,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
 elapsed=time.monotonic()-start
 d={'status':'PASS_ALL_SELECTED_DECLARATION_AXIOMS' if r.returncode==0 and stable() and h(source)==source_hash else 'FAILED_CERTIFICATE_AUDIT_SIDECAR','exit_code':r.returncode,'elapsed_seconds':elapsed,'command':command,'source_sha256':source_hash,'frozen_snapshot':'snapshots/'+version,'receipt_directory':str(out.relative_to(ROOT)),'log_sha256':h(out/'build.log'),'compiler':'4.33.1 commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6','selected_source_config_artifacts_stable':stable(),'distinct_theorems_not_equivalent_to_independent_claims':True}
 if r.returncode==0:
  d['report_sha256']=h(report);q=json.loads(report.read_text());d.update({k:q[k] for k in ['declaration_count','theorem_declaration_count','missing_modules','nonstandard_axiom_rows']});d['declaration_kind_counts']=dict(collections.Counter(x['kind'] for x in q['declarations']));d['owned_axiom_declarations']=[x['name'] for x in q['declarations'] if x['kind']=='axiom'];d['selected_module_count_including_aggregate']=len(modules)
 (out/'receipt.json').write_text(json.dumps(d,indent=2)+'\n')
 (ROOT/'receipts/ALL-DECLARATIONS-LATEST.json').write_text(json.dumps(d,indent=2)+'\n')
 print(json.dumps(d,indent=2));print((out/'build.log').read_text()[-2000:]);raise SystemExit(0 if d['status'].startswith('PASS') else 1)
