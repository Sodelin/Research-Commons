"""Syntax-checked public convenience runner; not the recorded author replay."""
import argparse,pathlib,os,subprocess,json,shutil
p=argparse.ArgumentParser();p.add_argument('--lean',required=True);p.add_argument('--dependency-path',required=True);p.add_argument('--output',required=True);a=p.parse_args()
R=pathlib.Path(__file__).resolve().parent;D=pathlib.Path(a.output);D.mkdir(exist_ok=False)
for sub in ['sources','build','evidence']:(D/sub).mkdir()
orders={".":['G5ActualActivatedPrefix', 'G5ActivatedPosteriorPlacement', 'G5OriginalEpochChart', 'G5PhysicalCutChart', 'G5PhysicalCutConditionalLaw', 'G5PhysicalCutAudit', 'G5OlderSideCutChart', 'G5OlderSideCutConditionalLaw', 'G5OlderSideCutAudit']}
for stage,mods in orders.items():
 for m in mods:
  src=R/stage/'sources'/f'{m}.lean';target=D/'sources'/src.name;shutil.copyfile(src,target)
  q=subprocess.run([a.lean,'--trust=0','-j1','-M4096','-Ddebug.skipKernelTC=false','-o',str((D/'build'/f'{m}.olean').resolve()),str(target.resolve())],cwd=D/'sources',env=dict(os.environ,LEAN_PATH=str((D/'build').resolve())+os.pathsep+a.dependency_path),capture_output=True,text=True)
  for ext,txt in [('stdout',q.stdout),('stderr',q.stderr)]: (D/'evidence'/f'{m}.{ext}').write_text(txt)
  (D/'evidence'/f'{m}.json').write_text(json.dumps({'exit_code':q.returncode,'module':m})+'\n')
  print(m,q.returncode,flush=True)
  if q.returncode:raise SystemExit(q.returncode)
