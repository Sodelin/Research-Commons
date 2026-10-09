"""Syntax-checked public convenience runner; not the recorded author replay."""
import argparse,pathlib,os,subprocess,json,shutil
p=argparse.ArgumentParser();p.add_argument('--lean',required=True);p.add_argument('--dependency-path',required=True);p.add_argument('--output',required=True);a=p.parse_args()
R=pathlib.Path(__file__).resolve().parent;D=pathlib.Path(a.output);D.mkdir(exist_ok=False)
for sub in ['sources','build','evidence']:(D/sub).mkdir()
orders={'natural-cut':['G5NaturalCutConsumer','G5NaturalObservedCutMass','G5NaturalCutAudit'],'two-cut':['G5TwoCutSourceWord','G5TwoCutCompletedSource','G5ObservedBinHistory','G5TwoCutAudit'],'posterior':['G5SourcePairPersistence','G5ConstantTagSource','G5TaggedWordProgram','G5CompletionPairPersistence','G5ThreePhaseCompletion','G5TwoCutProgramSupport','G5TwoCutPartitionDecoder','G5ActualTwoCutPartitionLaw','G5ActualDiscreteCutEvent','G5ObservedTwoCutPartitionLaw','G5ObservedCutPosterior','G5PosteriorJointCell','G5ActualConditionalPartition','G5PosteriorAssemblyAudit']}
for stage,mods in orders.items():
 for m in mods:
  src=R/stage/'sources'/f'{m}.lean';target=D/'sources'/src.name;shutil.copyfile(src,target)
  q=subprocess.run([a.lean,'--trust=0','-j1','-M4096','-Ddebug.skipKernelTC=false','-o',str((D/'build'/f'{m}.olean').resolve()),str(target.resolve())],cwd=D/'sources',env=dict(os.environ,LEAN_PATH=str((D/'build').resolve())+os.pathsep+a.dependency_path),capture_output=True,text=True)
  for ext,txt in [('stdout',q.stdout),('stderr',q.stderr)]: (D/'evidence'/f'{m}.{ext}').write_text(txt)
  (D/'evidence'/f'{m}.json').write_text(json.dumps({'exit_code':q.returncode,'module':m})+'\n')
  print(m,q.returncode,flush=True)
  if q.returncode:raise SystemExit(q.returncode)
