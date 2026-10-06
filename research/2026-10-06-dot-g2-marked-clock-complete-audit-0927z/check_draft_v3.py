#!/usr/bin/env python3
"""A single bounded ordinary compile, bound to an independently pinned manifest."""
import argparse,hashlib,json,os,pathlib,re,signal,subprocess,time,traceback
P=pathlib.Path(__file__).resolve().parent;R=P.parent;B=R/'provider-base'
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean')
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def bundle(base):return {s:sha(pathlib.Path(str(base)+s)) for s in SUFFIXES if pathlib.Path(str(base)+s).is_file()}
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--inputs',required=True);ap.add_argument('--inputs-sha256',required=True);args=ap.parse_args()
 inputs=pathlib.Path(args.inputs).resolve();assert sha(inputs)==args.inputs_sha256
 pins=json.loads(inputs.read_text());assert pins['schema']=='ordinary-draft-inputs-v3'
 def check_pins():
  assert sha(inputs)==args.inputs_sha256
  for relative,want in pins['files'].items():
   path=R/relative;assert not path.is_symlink() and path.resolve().is_relative_to(R)
   assert sha(path)==want,('input pin',relative)
 check_pins();assert pins['files'][str(pathlib.Path(__file__).resolve().relative_to(R))]==sha(__file__)
 runs=P/'ordinary';runs.mkdir(exist_ok=True)
 run=runs/('attempt-%03d'%(len(list(runs.iterdir()))+1));run.mkdir(exist_ok=False)
 result={'status':'RUNNING','historical_evidence':False,'input_manifest_sha256':args.inputs_sha256};start=time.monotonic();proc=None
 dump(run/'INPUTS.json',pins)
 try:
  terminal=B/'new-run-01/TERMINAL.json';terminal_sha=sha(terminal)
  td=json.loads(terminal.read_text());assert td['status']=='PASS_NEW_PROVIDER_COMPILATION'
  completed={d['module']:d['receipt_sha256'] for d in td['completed']}
  graph=json.loads((B/'SOURCE-GRAPH.json').read_text());expected={};bases={};roots=set()
  for e in json.loads((R/'RESTORED-EXTERNAL-ARTIFACTS.json').read_text()):
   expected.setdefault(e['module'],{})[e['suffix']]=e['sha256'];base=pathlib.Path(e['path'][:-len(e['suffix'])]);bases[e['module']]=base;roots.add(base.parents[len(e['module'].split('.'))-1])
  obj=B/'new-run-01/objects';paths=[obj]+sorted(roots,key=str)
  for row in graph['modules']:
   m=row['module'];assert sha(B/row['source_path'])==row['source_sha256']
   receipt=B/'new-run-01/logs'/(m+'.receipt.json');assert sha(receipt)==completed[m]
   d=json.loads(receipt.read_text());assert d['exit_code']==0 and not d['timeout']
   expected[m]=d['outputs'];bases[m]=obj/pathlib.Path(*m.split('.'))
  for row in pins.get('owned_imports',[]):
   m=row['module'];assert m not in expected
   assert row['receipt'] in pins['files'] and row['source'] in pins['files']
   d=json.loads((R/row['receipt']).read_text());assert d['status']=='PASS_ORDINARY_ONLY' and d['exit_code']==0 and not d.get('timeout',False)
   assert d['source_sha256']==pins['files'][row['source']]
   root=R/row['object_root'];assert root.resolve().is_relative_to(R)
   expected[m]=d['outputs'];bases[m]=root/pathlib.Path(*m.split('.'));paths.insert(0,root)
  def resolve(m):
   for root in paths:
    base=root/pathlib.Path(*m.split('.'))
    if pathlib.Path(str(base)+'.olean').is_file():return base
   raise RuntimeError('unknown import '+m)
  def check():
   check_pins()
   for m,e in expected.items():assert resolve(m)==bases[m] and bundle(bases[m])==e,('bundle',m)
  lean=R/'toolchain/lean-4.33.1-linux/bin/lean';source=R/pins['source']
  assert str(source.relative_to(R)) in pins['files']
  frozen=run/source.name;frozen.write_bytes(source.read_bytes());source_sha=sha(frozen)
  assert source_sha==pins['files'][pins['source']]
  imports=re.findall(r'^import\s+(\S+)\s*$',frozen.read_text(),re.M);assert imports
  check();binding={m:{'base':str(resolve(m)),'bundle':expected[m]} for m in imports}
  env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths));env['LEAN_NUM_THREADS']='1'
  cmd=[str(lean),'-j','1','-M','4096','-o',str(run/(source.stem+'.olean')),'-i',str(run/(source.stem+'.ilean')),str(frozen)]
  with (run/'stdout').open('wb') as out,(run/'stderr').open('wb') as err:
   proc=subprocess.Popen(cmd,cwd=run,env=env,stdout=out,stderr=err,start_new_session=True)
   try:code=proc.wait(timeout=180)
   except subprocess.TimeoutExpired:
    os.killpg(proc.pid,signal.SIGKILL);code=proc.wait();result['timeout']=True
  check();assert sha(frozen)==source_sha
  result.update(status='PASS_ORDINARY_ONLY' if code==0 else 'COMPILE_ERROR',exit_code=code,source_sha256=source_sha,direct_imports=binding,outputs=bundle(run/source.stem),stdout_sha256=sha(run/'stdout'),stderr_sha256=sha(run/'stderr'),command=cmd,provider_terminal_sha256=terminal_sha)
 except BaseException as e:
  if proc is not None and proc.poll() is None:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
  result.update(status='ERROR',error=repr(e),traceback=traceback.format_exc());raise
 finally:
  result['seconds']=time.monotonic()-start;dump(run/'RECEIPT.json',result);print(str(run),result['status'],flush=True)
if __name__=='__main__':main()
