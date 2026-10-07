from __future__ import annotations
import hashlib,json,os,platform,subprocess,sys,time
from datetime import datetime,timezone
from pathlib import Path

HERE=Path(__file__).resolve().parent
REF='2aeb123fb53b61594a1cf5b0542daf953cf90ab3'
BASE='research/2026-10-07-astra-g6-source-poisson-prefix-124833z'
EXPECTED={'finite_source_prefix.py':'cda900a655dd8dd4ae652e51c46fa0f37509bdc6','test_finite_source_prefix.py':'d413ff57280651569bd6e10e5560e450e6f80d9c','forest_pair_controls.py':'7bf9ce8b88c775da21da8ed32923c37cf96b8a5e'}

def utc(): return datetime.now(timezone.utc).isoformat()
def identity(name):
 b=(HERE/name).read_bytes(); blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 return {'bytes':len(b),'git_blob_sha1':blob,'expected_git_blob_sha1':EXPECTED[name],'verified_exact_git_blob':blob==EXPECTED[name],'sha256':hashlib.sha256(b).hexdigest(),'repository_url':'https://github.com/Sodelin/Research-Commons/blob/'+REF+'/'+BASE+'/'+name}
def write_new(path,data):
 with path.open('xb') as f: f.write(data)
 os.chmod(path,0o444)
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

(HERE/'evidence').mkdir(exist_ok=True)
initial={n:identity(n) for n in EXPECTED}
assert all(x['verified_exact_git_blob'] for x in initial.values())
write_new(HERE/'SOURCE-IDENTITIES.json',(json.dumps({'observed_utc':utc(),'source_commit':REF,'sources':initial,'fetch':'GitHub connector UTF-8 contents reconstructed into new scratch directory; Git blob verification confirms exact bytes.'},indent=2)+'\n').encode())
summaries=[]
for slug,script,args,expected_count,outfile in [('reference-1143','test_finite_source_prefix.py',[],1143,HERE/'evidence/reference-tests.json'),('forest-770','forest_pair_controls.py',['--output',str(HERE/'evidence/forest-pair-controls-fresh-replay.json')],770,HERE/'evidence/forest-pair-controls-fresh-replay.json')]:
 assert not outfile.exists(),str(outfile)
 argv=[sys.executable,script]+args
 started,t0=utc(),time.monotonic(); timeout=False
 try:
  result=subprocess.run(argv,cwd=HERE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180,check=False)
  stdout,stderr,exitcode=result.stdout,result.stderr,result.returncode
 except subprocess.TimeoutExpired as e:
  stdout,stderr,exitcode=e.stdout or b'',e.stderr or b'',None; timeout=True
 finished,elapsed=utc(),time.monotonic()-t0
 stdout_path,stderr_path=HERE/(slug+'.stdout.log'),HERE/(slug+'.stderr.log')
 write_new(stdout_path,stdout);write_new(stderr_path,stderr)
 report=None; parse_error=None
 if outfile.exists():
  try: report=json.loads(outfile.read_text())
  except Exception as e: parse_error=repr(e)
  os.chmod(outfile,0o444)
 after={n:identity(n) for n in EXPECTED}
 unchanged=after==initial
 passed=exitcode==0 and not timeout and report is not None and report.get('checks')==expected_count and unchanged
 receipt={'status':'PASS_FRESH_REFERENCE_REPLAY_NOT_LEAN' if passed else 'FAIL_OR_INCOMPLETE_FRESH_REFERENCE_REPLAY','execution_class':'NEW_EXECUTION_RECONSTRUCTED_FROM_EXACT_COMMITTED_SOURCE','historical_output_recovered':False,'source_commit':REF,'started_utc':started,'finished_utc':finished,'elapsed_seconds':round(elapsed,6),'timeout_seconds':180,'timed_out':timeout,'argv':argv,'cwd':str(HERE),'exit_code':exitcode,'python':platform.python_version(),'python_executable':sys.executable,'platform':platform.platform(),'expected_control_count':expected_count,'observed_control_count':report.get('checks') if report else None,'control_status':report.get('status') if report else None,'sources_unchanged':unchanged,'source_identities':initial,'stdout_path':str(stdout_path),'stdout_sha256':digest(stdout_path),'stderr_path':str(stderr_path),'stderr_sha256':digest(stderr_path),'original_script_new_output_path':str(outfile) if outfile.exists() else None,'original_script_new_output_sha256':digest(outfile) if outfile.exists() else None,'parse_error':parse_error,'scope':'Exact finite rational controls only. This rerun does not recover historical stdout, prove all-size results, execute Lean, validate an original historical environment, or certify complete G6.'}
 receipt_path=HERE/(slug+'.NEW-EXECUTION-RECEIPT.json')
 write_new(receipt_path,(json.dumps(receipt,indent=2)+'\n').encode())
 summaries.append({k:receipt[k] for k in ['status','started_utc','finished_utc','elapsed_seconds','observed_control_count','control_status','exit_code'] }|{'receipt_path':str(receipt_path)})
 print(json.dumps(summaries[-1]),flush=True)
 if not passed: break
write_new(HERE/'REPLAY-SUMMARY.json',(json.dumps({'finished_utc':utc(),'executions':summaries,'historical_output_recovered':False},indent=2)+'\n').encode())
if len(summaries)!=2 or any(x['status']!='PASS_FRESH_REFERENCE_REPLAY_NOT_LEAN' for x in summaries): sys.exit(1)
