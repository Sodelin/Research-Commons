#!/usr/bin/env python3
"""Reproducible Lake build certificate for the explicitly selected closure."""
from pathlib import Path
import fcntl, hashlib, json, os, re, subprocess, sys, time
ROOT=Path(__file__).resolve().parents[1]
from toolchain import binary_dir
TOOL=binary_dir()
limit=int(sys.argv[1]) if len(sys.argv)>1 else 300
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot():
    paths=[ROOT/'UnifiedLean.lean',ROOT/'lakefile.lean',ROOT/'lean-toolchain',ROOT/'lake-manifest.json']
    manifest=json.loads((ROOT/'catalog/COMBINED-IMPORT-BASELINE.json').read_text())
    paths += [ROOT/'Imported'/Path(*m.split('.')).with_suffix('.lean') for m in manifest['flat_modules']]
    paths += [ROOT/Path(*m.split('.')).with_suffix('.lean') for m in manifest['canonical_new_modules']]
    paths += [ROOT/manifest['historical_module_paths'][m] for m in manifest.get('historical_modules',[])]
    return {str(p.relative_to(ROOT)):h(p) for p in sorted(paths)}
with (ROOT/'.build.lock').open('a') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX)
    before=snapshot();stamp=str(time.time_ns());out=ROOT/'receipts'/('lake-build-'+stamp)
    out.mkdir(parents=True);log=out/'build.log'
    env=os.environ.copy();env['PATH']=str(TOOL)+':'+env.get('PATH','');env['LEAN_NUM_THREADS']='1'
    command=['timeout',str(limit),str(TOOL/'lake'),'--no-cache','build','UnifiedLean']
    start=time.monotonic()
    with log.open('w') as f:r=subprocess.run(command,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
    elapsed=time.monotonic()-start;after=snapshot();text=log.read_text()
    ax=[' '.join(x.split()) for x in re.findall(r"'[^']+' depends on axioms: \[.*?\]|'[^']+' does not depend on any axioms",text,re.S)]
    bad=[]
    for line in ax:
        m=re.search(r'\[(.*?)\]',line)
        if m:bad += [a.strip() for a in m.group(1).split(',') if a.strip() not in {'propext','Classical.choice','Quot.sound'}]
    imported=json.loads((ROOT/'catalog/COMBINED-IMPORT-BASELINE.json').read_text())
    modules=imported['flat_modules']+imported['canonical_new_modules']+imported.get('historical_modules',[])+['UnifiedLean']
    artifacts={}
    for module in modules:
        p=ROOT/'.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')
        if p.exists():artifacts[module]=h(p)
    accepted=r.returncode==0 and before==after and not bad and len(artifacts)==len(modules)
    receipt={'status':'PASS_SELECTED_LAKE_IMPORT_CLOSURE' if accepted else 'FAILED_OR_CHANGED_LAKE_BUILD',
      'command':command,'exit_code':r.returncode,'elapsed_seconds':elapsed,
      'compiler':'Lean4.33.1 commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6',
      'mathlib_commit':'0df444a360eaa60ab8c11dca51a86af692955474',
      'source_and_config_sha256':before,'source_and_config_stable':before==after,
      'module_count_excluding_aggregate':len(modules)-1,'artifact_sha256':artifacts,
      'printed_axiom_audits':len(ax),'axiom_lines':ax,'nonstandard_axioms':sorted(set(bad)),
      'log_sha256':h(log),'receipt_directory':str(out.relative_to(ROOT)),
      'full_project_source_correctness_claim':False,'historical_source_coverage_complete_claim':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (ROOT/'receipts/LAKE-BUILD-LATEST.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in {'source_and_config_sha256','artifact_sha256','axiom_lines'}},indent=2))
    print(text[-8000:]);raise SystemExit(0 if accepted else 1)
