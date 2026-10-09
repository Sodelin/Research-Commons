"""Portable reproduction runner. Syntax checked; not the runner used for historical receipts.
Requires a separately prepared pinned Lean/mathlib/baseline runtime. No installer.
Run serially: python build_g5_portable.py --runtime /path/to/runtime
"""
import argparse,hashlib,json,os,pathlib,subprocess,sys,time
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--runtime', type=pathlib.Path, required=True)
parser.add_argument('--output', type=pathlib.Path, required=True, help='Fresh output directory, separate from packet and baseline')
parser.add_argument('modules', nargs='*')
args=parser.parse_args()
R=pathlib.Path(__file__).resolve().parent
T=args.runtime.resolve()
O=args.output.resolve()
if O.exists(): parser.error('--output must not already exist')
for required in [T/'lean-4.33.1-linux/bin/lean', T/'mathlib/.lake/build/lib/lean', T/'baseline181-build']:
 if not required.exists(): parser.error('Missing prepared dependency: '+str(required))
S=R/'sources'; B=O/'build'; E=O/'evidence'; B.mkdir(parents=True);E.mkdir()
# File-level read-only dependency overlay avoids Lean namespace shadowing.
for p in (T/'baseline181-build').rglob('*.olean'):
 q=B/p.relative_to(T/'baseline181-build');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p.resolve())
order=['UnifiedLean.Source.SourceCrossCarrierNatural','G5OriginalProgramSurvival','G5OriginalSelectedPosterior','G5OriginalConditionedContinuation','G5ActualNoMergerReadout','G5SelectedSingletonCarrier','G5SelectedDiscreteSurvival','G5SelectedSingletonRates','G5TriplePartitionReadout','G5ActualTripleMoments','G5TripleMomentReconstruction','G5ActualFrozenTripleRow','G5ActualPosteriorGerm','G5IntegrationAudit']
M=T/'mathlib';paths=[B,T/'baseline181-build',M/'.lake/build/lib/lean']+[x/'.lake/build/lib/lean' for x in (M/'.lake/packages').iterdir() if x.is_dir()]
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths)),PATH=str(T/'lean-4.33.1-linux/bin')+':'+os.environ['PATH'])
selected=args.modules or order
records=[]
for mod in selected:
 assert mod in order
 p=S/(mod.replace('.','/')+'.lean'); o=B/(mod.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
 # Never write through a baseline object symlink.
 if o.is_symlink(): o.unlink()
 stamp=time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())+'-'+str(time.time_ns()%1000000)
 label=stamp+'-'+mod;cmd=[str(T/'lean-4.33.1-linux/bin/lean'),'--trust=0','-j1','-M4096','-Ddebug.skipKernelTC=false','-o',str(o),str(p)]
 start=time.time()
 with open(E/(label+'.stdout'),'w') as out,open(E/(label+'.stderr'),'w') as err:
  try: q=subprocess.run(cmd,cwd=S,env=env,stdout=out,stderr=err,timeout=180);code=q.returncode
  except subprocess.TimeoutExpired: code=124
 rec={'module':mod,'command':cmd,'exit_code':code,'seconds':time.time()-start,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'object_sha256':hashlib.sha256(o.read_bytes()).hexdigest() if code==0 and o.exists() else None,'stdout':label+'.stdout','stderr':label+'.stderr'}
 (E/(label+'.json')).write_text(json.dumps(rec,indent=2)+'\n');records.append(rec)
 print(json.dumps(rec),flush=True)
 if code: raise SystemExit(code)
(E/(stamp+'-batch.json')).write_text(json.dumps({'records':records,'mathlib':'official cache','baseline':'separate fresh verified source objects','full_axiom_audit':'pending'},indent=2)+'\n')
