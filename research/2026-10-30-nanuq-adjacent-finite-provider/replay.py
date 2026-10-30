from pathlib import Path
import subprocess,os,json,time,hashlib
import argparse
parser=argparse.ArgumentParser(description='Replay the exact selected Lean source closure without installing dependencies.')
parser.add_argument('--source-root',type=Path,default=Path(__file__).parent)
parser.add_argument('--lean',type=Path,required=True)
parser.add_argument('--dependency-olean-dir',type=Path,action='append',required=True)
args=parser.parse_args();root=args.source_root.resolve();lean=args.lean.resolve()
manifest=json.loads((root/'SOURCE-MANIFEST.json').read_text())
version=subprocess.check_output([str(lean),'--version'],text=True)
assert 'version 4.33.1' in version, version
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(root)]+[str(p.resolve()) for p in args.dependency_olean_dir])
logdir=root/'build-logs';logdir.mkdir(exist_ok=True)
receipt=root/'BUILD-EVENTS.jsonl'
manifest_sha=hashlib.sha256((root/'SOURCE-MANIFEST.json').read_bytes()).hexdigest()
startfile=root/'BUILD-START.json'
if startfile.exists():assert json.loads(startfile.read_text())['source_manifest_sha256']==manifest_sha
else:startfile.write_text(json.dumps({'source_manifest_sha256':manifest_sha,'compiler_sha256':hashlib.sha256(lean.read_bytes()).hexdigest(),'mode':'isolated local closure, kernel checked'},indent=2)+'\n')
accepted={}
if receipt.exists():
 for line in receipt.read_text().splitlines():
  item=json.loads(line)
  if item['exit']==0:accepted[item['module']]=item
for module in manifest['order']:
 src=root/(module+'.lean');sha=hashlib.sha256(src.read_bytes()).hexdigest();assert sha==manifest['modules'][module]['source_sha256']
 if module in accepted:
  old=accepted[module];obj=root/(module+'.olean')
  if old['source_sha256']==sha and obj.exists() and hashlib.sha256(obj.read_bytes()).hexdigest()==old['olean_sha256']:
   print('ALREADY ACCEPTED '+module,flush=True);continue
 budget='2800' if module.startswith('NodeRow_6_63_') else '1800'
 start=time.time()
 log=logdir/(module+'.log')
 if log.exists():log.rename(logdir/(module+'.previous-'+str(time.time_ns())+'.log'))
 with log.open('w') as out:
  proc=subprocess.run([str(lean),'-M',budget,'-o',module+'.olean',module+'.lean'],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
 after=hashlib.sha256(src.read_bytes()).hexdigest();assert after==sha
 row={'module':module,'source_sha256':sha,'exit':proc.returncode,'seconds':time.time()-start,'memory_limit_mb':int(budget)}
 if proc.returncode==0:row['olean_sha256']=hashlib.sha256((root/(module+'.olean')).read_bytes()).hexdigest()
 with receipt.open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
 if proc.returncode:raise SystemExit('CLEAN BUILD FAILED '+module)
final=(logdir/'FiniteProvider.log').read_text()
assert 'sorryAx' not in final and 'ofReduceBool' not in final
(root/'BUILD-ACCEPTANCE.json').write_text(json.dumps({'status':'PASS_SCOPED_FINITE_PROVIDER_NOT_FULL_NANUQ','modules':len(manifest['order']),'source_manifest_sha256':hashlib.sha256((root/'SOURCE-MANIFEST.json').read_bytes()).hexdigest(),'axiom_log':final,'kernel_checking':'debug.skipKernelTC false; decide +kernel; no native_decide','source_plane_bridge':'OPEN','arbitrary_size_restriction_bridge':'OPEN'},indent=2)+'\n')
print('CLEAN ACCEPTANCE COMPLETE',flush=True)
