#!/usr/bin/env python3
"""Single-process replay and complete owned-declaration axiom audit.
Pass --lean and --dependency-roots, or supply THETA_LEAN_BIN and
THETA_OBJECT_ROOTS from an already provisioned pinned environment.
No dependencies are downloaded and no build outside this package is changed.
"""
import argparse, hashlib, json, os, re, subprocess, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
SOURCES=[
 'SamuelAlexanderResearch/ThueMorseBits.lean',
 'ThueMorseMAP/Basic.lean', 'ThueMorseMAP/Blocks.lean',
 'ThueMorseMAP/OddMinus.lean', 'ThueMorseMAP/EvenMinus.lean',
 'ThueMorseMAP/Plus.lean', 'ThueMorseMAP/Headline.lean',
]
EXPECTED_VERSION='4.33.1'
EXPECTED_MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
 p=argparse.ArgumentParser()
 p.add_argument('--lean',default=str(Path(os.environ.get('THETA_LEAN_BIN',''))/'lean'))
 p.add_argument('--dependency-roots',default=os.environ.get('THETA_OBJECT_ROOTS',''))
 p.add_argument('--output',default='verification')
 args=p.parse_args()
 out=ROOT/args.output;out.mkdir(parents=True,exist_ok=True)
 objects=out/'objects';objects.mkdir(exist_ok=True)
 env=dict(os.environ,LEAN_PATH=str(objects)+':'+args.dependency_roots,LEAN_NUM_THREADS='1')
 version=subprocess.run([args.lean,'--version'],text=True,capture_output=True,check=True).stdout.strip()
 assert EXPECTED_VERSION in version,version
 assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version,version
 mathlib_root=Path(args.dependency_roots.split(':')[0]).resolve().parents[3]
 mathlib_commit=subprocess.run(['git','-C',str(mathlib_root),'rev-parse','HEAD'],text=True,capture_output=True,check=True).stdout.strip()
 assert mathlib_commit==EXPECTED_MATHLIB,mathlib_commit
 receipts=[];names=[]
 for rel in SOURCES:
  src=ROOT/rel; data=src.read_text()
  # This package intentionally uses no proof bypass or additional axioms.
  assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b',data),rel
  assert not re.search(r'^\s*axiom\s',data,re.M),rel
  ns='ThueMorseBits' if rel.startswith('Samuel') else 'ThueMorseMAP'
  declared=re.findall(r'^(?:@\[[^\n]*\]\s+)?(?:noncomputable\s+)?(?:def|theorem)\s+([\w.]+)',data,re.M)
  names.extend(ns+'.'+x for x in declared)
  dest=(objects/rel).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  start=time.monotonic()
  result=subprocess.run([args.lean,'-j1','-M4096','-o',str(dest),str(src)],cwd=ROOT,env=env,text=True,capture_output=True)
  log=out/(rel.replace('/','__')+'.log');log.write_text(result.stdout+result.stderr)
  receipts.append({'path':rel,'sha256':digest(src),'returncode':result.returncode,'seconds':round(time.monotonic()-start,3),'log':str(log.relative_to(ROOT)),'object_sha256':digest(dest) if dest.exists() else None})
  if result.returncode:raise RuntimeError(f'{rel} failed; see {log}')
 assert len(names)==len(set(names))
 audit=out/'OwnedAxioms.lean'
 audit.write_text('import ThueMorseMAP.Headline\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
 result=subprocess.run([args.lean,'-j1','-M4096',str(audit)],cwd=ROOT,env=env,text=True,capture_output=True)
 log=result.stdout+result.stderr;(out/'owned-axioms.log').write_text(log)
 if result.returncode:raise RuntimeError('Axiom audit failed')
 records=[]
 for name in names:
  match=re.search(r"'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",log)
  no_axioms=f"'{name}' does not depend on any axioms" in log
  assert match or no_axioms,('missing axiom line',name)
  axioms=[] if no_axioms else [a.strip() for a in match.group(1).split(',') if a.strip()]
  assert set(axioms)<=ALLOWED,(name,axioms)
  records.append({'name':name,'axioms':axioms})
 full_audit=ROOT/'scripts/FullAxiomAudit.lean'
 env['TM_AUDIT_REPORT']=str(out/'FULL-OWNED-AXIOMS.json')
 full=subprocess.run([args.lean,'-j1','-M4096',str(full_audit)],cwd=ROOT,env=env,text=True,capture_output=True)
 (out/'full-owned-axioms.log').write_text(full.stdout+full.stderr)
 if full.returncode:raise RuntimeError('Full module-owned axiom audit failed')
 full_result=json.loads((out/'FULL-OWNED-AXIOMS.json').read_text())
 assert full_result['missing_modules']==[] and full_result['nonstandard_axiom_rows']==[]
 receipt={'status':'PASS','scope':'All seven source modules plus every explicitly declared owned/imported-provider definition and theorem. Uniform source formulas are in Headline.lean.','lean_version':version,'verified_mathlib_commit':mathlib_commit,'source_builds':receipts,'audited_declarations':records,'full_module_owned_declaration_count':full_result['declaration_count'],'full_module_owned_axiom_receipt_sha256':digest(out/'FULL-OWNED-AXIOMS.json'),'audit_source_sha256':digest(full_audit),'custom_axioms':[],'proof_bypass_scan':'PASS','script_sha256':digest(Path(__file__))}
 (out/'BUILD-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({'status':'PASS','sources':len(SOURCES),'explicit_declarations':len(names),'full_module_declarations':full_result['declaration_count'],'receipt':str((out/'BUILD-RECEIPT.json').relative_to(ROOT))},indent=2))

if __name__=='__main__':main()
