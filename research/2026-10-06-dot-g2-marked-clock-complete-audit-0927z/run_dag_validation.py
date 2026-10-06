#!/usr/bin/env python3
"""One pinned, bounded, task-local DAG validation with an immutable receipt."""
import argparse,hashlib,json,os,pathlib,resource,signal,subprocess,sys,time,traceback
P=pathlib.Path(__file__).resolve().parent;R=P.parent
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--inputs',required=True);ap.add_argument('--inputs-sha256',required=True);a=ap.parse_args()
 f=pathlib.Path(a.inputs).resolve();assert sha(f)==a.inputs_sha256;m=json.loads(f.read_text())
 assert m['schema']=='bounded-dag-validation-v1'
 def check():
  assert sha(f)==a.inputs_sha256
  for p,h in m['files'].items():
   q=R/p;assert q.resolve().is_relative_to(R) and not q.is_symlink();assert sha(q)==h,p
 check();assert m['files'][str(pathlib.Path(__file__).resolve().relative_to(R))]==sha(__file__)
 run=R/m['output_directory'];assert run.resolve().is_relative_to(R);run.mkdir(exist_ok=False)
 assert len(m['audits']) in (1,2) and all(p in m['files'] for p in m['audits'])
 assert m['validator'] in m['files']
 cmd=[sys.executable,str(R/m['validator'])]+[str(R/p) for p in m['audits']]
 result={'status':'RUNNING','inputs_sha256':a.inputs_sha256,'command':cmd,'memory_limit_bytes':1073741824,'wall_seconds':60};start=time.monotonic();proc=None
 try:
  def limit():resource.setrlimit(resource.RLIMIT_AS,(1073741824,1073741824))
  with (run/'stdout').open('wb') as out,(run/'stderr').open('wb') as err:
   proc=subprocess.Popen(cmd,stdout=out,stderr=err,cwd=R,start_new_session=True,preexec_fn=limit)
   try:code=proc.wait(timeout=60)
   except subprocess.TimeoutExpired:
    os.killpg(proc.pid,signal.SIGKILL);code=proc.wait();result['timeout']=True
  check();result.update(status='PASS' if code==0 else 'FAIL',exit_code=code,stdout_sha256=sha(run/'stdout'),stderr_sha256=sha(run/'stderr'))
 except BaseException as e:
  if proc is not None and proc.poll() is None:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
  result.update(status='ERROR',error=repr(e),traceback=traceback.format_exc());raise
 finally:
  result['seconds']=time.monotonic()-start;(run/'RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n');print(run,result['status'],flush=True)
if __name__=='__main__':main()
