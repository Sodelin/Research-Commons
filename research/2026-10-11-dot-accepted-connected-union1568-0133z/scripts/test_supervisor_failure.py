"""Inject an accounting race into the real supervisor around a harmless sleeper."""
from pathlib import Path
import tempfile,json,sys,subprocess
import run_union as s
from completed_trace_transport import sha
P=Path(__file__).resolve().parents[1];results=[]
for kind in ['missing_path','unexpected_accounting_error']:
 with tempfile.TemporaryDirectory(dir=P,prefix='supervisor-control-') as td:
  root=Path(td);(root/'DEPENDENCY-GRAPH.json').write_text(json.dumps({'targets':{'test':{'modules':{}}}}));(root/'PREPARATION.json').write_text(json.dumps({'graph_sha256':sha(root/'DEPENDENCY-GRAPH.json'),'source_bytes':0,'new_source_bytes':0,'scripts':{'build_connected.py':'fixture'}}))
  s.ROOT=root;s.available=lambda:8*2**30;s.compress_completed=lambda *a,**kw:0
  class D:free=30*2**30
  s.shutil.disk_usage=lambda _:D()
  calls=[0]
  def allocation(_):
   calls[0]+=1
   if calls[0]==3:
    if kind=='missing_path':raise FileNotFoundError('injected staging rename')
    raise RuntimeError('injected unreadable accounting')
   return 0,0
  s.allocated=allocation
  real=subprocess.Popen;children=[]
  def launch(cmd,**kw):
   child=real([sys.executable,'-c','import time;time.sleep(60)'],**kw);children.append(child);return child
  s.subprocess.Popen=launch
  sys.argv=['test','--mathlib',str(root),'--lean-bin',str(root),'--target','test']
  try:rc=s.main()
  finally:s.subprocess.Popen=real
  assert rc==1 and children[0].poll() is not None
  receipt=json.loads(next(root.glob('SUPERVISOR-*.json')).read_text());assert receipt['limit_event'].startswith('SUPERVISOR_EXCEPTION:')
  results.append({'control':kind,'supervisor_exit':rc,'child_exit':children[0].returncode,'terminal_receipt_saved':True})
report={'status':'PASS','compiler_invoked':False,'controls':results,'supervisor_sha256':sha(P/'scripts/run_union.py')};(P/'SUPERVISOR-FAILURE-CONTROLS.json').write_text(json.dumps(report,indent=2)+'\n')
