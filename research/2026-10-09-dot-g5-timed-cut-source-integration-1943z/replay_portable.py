"""Fresh-output G5 replay. Configurable dependency roots; preserves prior evidence."""
import os, pathlib, subprocess, json, hashlib, time, sys, shutil
R=pathlib.Path(__file__).resolve().parent
T=pathlib.Path(os.environ.get('LEAN_RUNTIME','/workspace/shared/lean-runtime-20261009'))
M=pathlib.Path(os.environ.get('MATHLIB_ROOT',str(T/'mathlib')))
P=pathlib.Path(os.environ.get('G5_PRIOR_BUILD','/workspace/shared/g5-modular-integration-20261009-1754z/build'))
Q=pathlib.Path(os.environ.get('TIMED_PROVIDER_BUILD','/workspace/shared/g5-timed-provider-reuse-20261009-1925z/build'))
F=R/'sources'; C=R/'portable-clean-replay'
C.mkdir(exist_ok=False)
for d in ['sources','build','evidence']: (C/d).mkdir()
mods=['G5ActualNoEventEpoch','G5ObservedEpochConditioning','G5ActualRoutingSupport','G5StrictBoundaryRoutes','G5EnumeratedTripleRow','G5EnumeratedPosteriorGerm','G5TimedCutReadout','G5CutIntegrationAudit']
for mod in mods: shutil.copyfile(F/(mod+'.lean'),C/'sources'/(mod+'.lean'))
paths=[C/'build',Q,P,T/'baseline181-build',M/'.lake/build/lib/lean']+[x/'.lake/build/lib/lean' for x in sorted((M/'.lake/packages').iterdir()) if x.is_dir()]
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths))); rows=[]
for mod in mods:
 p=C/'sources'/(mod+'.lean'); cmd=[str(T/'lean-4.33.1-linux/bin/lean'),'--trust=0','-j1','-M4096','-Ddebug.skipKernelTC=false','-o',str(C/'build'/(mod+'.olean')),str(p)]
 start=time.time(); run=subprocess.run(cmd,cwd=C/'sources',env=env,capture_output=True,text=True,timeout=240)
 for suf,txt in [('stdout',run.stdout),('stderr',run.stderr)]: (C/'evidence'/(mod+'.'+suf)).write_text(txt)
 row=dict(module=mod,exit_code=run.returncode,seconds=time.time()-start,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),command=cmd)
 rows.append(row); (C/'evidence'/(mod+'.json')).write_text(json.dumps(row,indent=2)+'\n')
 (C/'REPLAY-RECEIPT.json').write_text(json.dumps(dict(rows=rows,all_pass=len(rows)==len(mods) and all(x['exit_code']==0 for x in rows),lean_path=paths),indent=2,default=str)+'\n')
 print(mod,run.returncode,flush=True)
 if run.returncode: print(run.stdout,run.stderr);sys.exit(run.returncode)
print('ALL_EIGHT_CLEAN_REPLAY_PASS',flush=True)
