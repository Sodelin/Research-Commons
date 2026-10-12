from pathlib import Path
import os,json,hashlib,shutil,subprocess,datetime,sys,time
from process_telemetry import Sampler
P=Path(__file__).resolve().parent
review=Path(sys.argv[1]);expected=sys.argv[2];attempt=int(sys.argv[3]);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if sha(review)!=expected:raise ValueError('independent review hash')
free=shutil.disk_usage(P).free;mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])*1024
active=sum(p.stat().st_blocks*512 for p in P.rglob('*') if p.is_file() and not p.is_symlink())
if free<=10*1024**3 or mem<7*1024**3:raise ValueError('fresh resource reserve')
if active+1024**3>=2*1024**3:raise ValueError('one GiB active-package run margin')
B='$LEAN/bin';env=os.environ.copy();env.update(CONNECTED_LEAN_BIN=B,CONNECTED_MATHLIB='$MATHLIB',PATH=B+':'+env['PATH'])
cmd=[B+'/lake','test','--','candidate/g4-paired-natural-tree-certificate'];now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat();stem='LAKE-ATTEMPT'+str(attempt)
meta=dict(command=cmd,started_utc=now(),review_sha256=expected,free_bytes=free,available_memory_bytes=mem,active_path_bytes=active,run_allowance_bytes=1024**3,profile='2GiB monitored package/8GiB floor; two exact sources plus aggregate/audit; each180s/4096MiB',graph_sha256=sha(P/'DEPENDENCY-GRAPH.json'),telemetry_script_sha256=sha(P/'process_telemetry.py'))
with (P/(stem+'-LAUNCH.json')).open('x') as f:json.dump(meta,f,indent=2)
sampler=Sampler(P/(stem+'-PROCESS-MEMORY.jsonl'))
with (P/(stem+'.stdout')).open('xb') as out,(P/(stem+'.stderr')).open('xb') as err:
 child=subprocess.Popen(cmd,cwd=P,env=env,stdout=out,stderr=err)
 (P/(stem+'-ACTIVE.json')).write_text(json.dumps(dict(pid=child.pid,started_utc=meta['started_utc']),indent=2)+'\n');print('Active Lake PID',child.pid,flush=True)
 while child.poll() is None:
  sampler.observe(child.pid);time.sleep(sampler.interval)
 sampler.observe(child.pid);rc=child.wait()
telemetry=sampler.finish(P/(stem+'-PROCESS-MEMORY-SUMMARY.json'))
meta.update(exit_code=rc,finished_utc=now(),telemetry_status=telemetry['status'],telemetry_samples=telemetry['samples']);(P/(stem+'-TERMINAL.json')).write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta),flush=True);sys.exit(rc if rc else (0 if telemetry['status']=='OBSERVATIONS_RECORDED' else 2))
