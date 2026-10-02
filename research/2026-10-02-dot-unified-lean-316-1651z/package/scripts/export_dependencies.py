#!/usr/bin/env python3
"""Export direct compiled proof/type references without inferring claim equivalence."""
from pathlib import Path
import json,hashlib,os,subprocess,time,fcntl,sys
from toolchain import binary_dir
ROOT=Path(__file__).resolve().parents[1];version=sys.argv[1];S=ROOT/'snapshots'/version;f=json.loads((S/'FREEZE.json').read_text())
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def stable():return all(h(S/p)==v for p,v in f['source_and_config_sha256'].items()) and all(h(S/'objects'/Path(*m.split('.')).with_suffix('.olean'))==v for m,v in f['artifact_sha256'].items())
with (ROOT/'.build.lock').open('a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX);assert stable();out=ROOT/'receipts'/('declaration-dependencies-'+version+'-'+str(time.time_ns()));out.mkdir();report=out/'dependencies.json';source=out/'export.lean'
 body=(ROOT/'checks/DeclarationDependencies.body').read_text();source.write_text('import UnifiedLean\nimport Lean.Util.FoldConsts\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let selected : Array String := #['+','.join(json.dumps(x) for x in sorted(f['artifact_sha256']))+']\n  let reportFile : String := '+json.dumps(str(report.relative_to(ROOT)))+'\n'+body)
 paths=[S/'objects',ROOT/'deps/mathlib/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (ROOT/'.lake/packages').iterdir() if p.is_dir()];env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,paths));tool=binary_dir();cmd=['timeout','60',str(tool/'lean'),'-j1','-M4096',str(source)];start=time.monotonic()
 with (out/'build.log').open('w') as log:r=subprocess.run(cmd,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
 d={'status':'PASS_COMPILED_DEPENDENCY_EXPORT' if r.returncode==0 and stable() else 'FAILED_DEPENDENCY_EXPORT','exit_code':r.returncode,'seconds':time.monotonic()-start,'snapshot':version,'source_sha256':h(source),'log_sha256':h(out/'build.log'),'frozen_source_config_objects_stable':stable(),'claim_equivalence_or_hand_acceptance_inferred':False,'directory':str(out.relative_to(ROOT))}
 if r.returncode==0:
  q=json.loads(report.read_text());d['report_sha256']=h(report);d['declaration_count']=q['declaration_count'];d['owned_body_edges']=sum(len(x['owned_body_references']) for x in q['declarations']);d['owned_type_edges']=sum(len(x['owned_type_references']) for x in q['declarations']);d['direct_head_delegation_candidates']=sum(bool(x['direct_head_delegation_candidate']) for x in q['declarations'])
 (out/'receipt.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2));print((out/'build.log').read_text()[-1500:]);raise SystemExit(0 if d['status'].startswith('PASS') else 1)
