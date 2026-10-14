#!/usr/bin/env python3
"""Bounded independent readback/monitor only; never launches/stops a process."""
import datetime, hashlib, json, os, resource, shutil, sys
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(20,20))
R=Path('/workspace/Research-Commons');S=R/'research/2026-10-13-astra-positive-support-adapter-0830z'; E=S/'evidence';D=R/'research/2026-10-13-astra-detached-serial-batch-2345z'; ST=Path('/workspace/scratch/astra-support-external-0840')
MON=E/'RUST-LANE-MONITOR-074-076.jsonl'
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def js(p):return json.loads(Path(p).read_text())
def save(p,x):
 with p.open('x') as f:json.dump(x,f,indent=2);f.write('\n')
def proc():
 names={'lean','lake','guard.py','build_external_serial.py','build_support.py','run_external_batches.py','run_external_batches_6g.py','run_provider_batches.py','diagnose_module.py','diagnose_thread_failure.py','one_guard.py','one_batch.py','one_batch_small.py','one_owned_batch.py','build_support_namespace.py','run_provider_namespace_batches.py','query_imports.py','capture_query.py'}
 out=[]
 for p in Path('/proc').iterdir():
  if not p.name.isdigit() or int(p.name)==os.getpid():continue
  try:
   parts=(p/'stat').read_text().rsplit(') ',1)[1].split();a=(p/'cmdline').read_bytes().rstrip(b'\0').decode().split('\0')
   if parts[0] not in ('Z','X') and any(Path(x).name in names for x in a):out.append(dict(pid=int(p.name),state=parts[0],starttime=parts[19],argv=a))
  except (FileNotFoundError,ProcessLookupError):pass
 return out
def sample(batch,append=True):
 out=E/f'external-batch-{batch:03d}'; events=[]
 if (out/'stdout').exists():
  for line in (out/'stdout').read_text().splitlines():
   try:x=json.loads(line)
   except json.JSONDecodeError:continue
   if 'index' in x and 'module' in x:events.append(x)
 gr=None
 if (out/'RECEIPT.json').exists():
  g=js(out/'RECEIPT.json');gr={k:g.get(k) for k in ['exit_code','stop','error','elapsed_seconds']};gr['sha256']=sha(out/'RECEIPT.json')
 m=dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),batch=batch,completed_count=len(events),last_completion=events[-1] if events else None,guard_receipt_exists=gr is not None,guard=gr,cgroup_bytes=int(Path('/sys/fs/cgroup/memory.current').read_text()),disk_free=shutil.disk_usage(R).free,memory_events=Path('/sys/fs/cgroup/memory.events').read_text(),pause=(S/'PAUSE-BUILDS').exists(),active_processes=proc())
 if append:
  with MON.open('a') as f:f.write(json.dumps(m)+'\n');f.flush();os.fsync(f.fileno())
 return m
PINS=js(E/'RUST-LANE-070-CLOSED.json')['source_pins']
def pins():
 for p,h in PINS.items():assert sha(p)==h,p
 return PINS
LIMITS=dict(cpu_seconds=600,wall_seconds=900,address_space_bytes=6*1024**3,file_bytes=1024**3,disk_floor=8*1024**3,ram_floor=1024**3,cgroup_stop=4*1024**3)
def closed(batch,start,count):
 pins();out=E/f'external-batch-{batch:03d}';dd=D/'evidence'/f'production-{batch:03d}'
 g=js(out/'RECEIPT.json');c=js(out/'MODULE-RECEIPTS.json');f=js(dd/'FINISH.json');it=js(dd/'INTENT.json');la=js(dd/'LAUNCH.json');pl=it['profile'];plan=js(S/'EXTERNAL-PLAN.json')['modules']
 assert g['exit_code']==0 and g['stop'] is None and not g.get('error')
 assert g['limits']==LIMITS and g['runner_sha256']==PINS[str(R/'research/2026-10-13-astra-unified-solver-0645z/guard.py')]
 assert pl['child_command']==g['command'] and pl['cwd']==g['cwd']==str(R)
 assert pl['limits']==LIMITS and pl['expected_start_index']==start and pl['fresh_budget']==count and pl['expected_fresh_count']==count and pl['batch_id']==batch
 assert pl['launcher_sha256']==PINS[str(D/'one_batch_small.py')]
 assert la['intent_sha256']==sha(dd/'INTENT.json') and f['launch_sha256']==sha(dd/'LAUNCH.json')
 assert f['status']=='GUARD_RECEIPT_SUCCESS' and not f['guard_error'] and not f['guard_stop'] and not f['requested_stop'] and f['builder_exit_code']==0
 assert c['guard_receipt_sha256']==f['guard_receipt_sha256']==sha(out/'RECEIPT.json') and f['capture_sha256']==sha(out/'MODULE-RECEIPTS.json')
 assert c['prebatch_inventory_sha256']==it['prebatch_sha256']==f['prebatch_sha256']==sha(dd/'PRE-BATCH-STATE.json')==sha(out/'PRE-BATCH-STATE.json')
 assert c['capture_runner_sha256']==PINS[str(S/'capture_batch.py')] and c['interrupted_unverified_invocations']==[]
 for n,v in g['outputs'].items():assert sha(out/n)==v['sha256'] and (out/n).stat().st_size==v['bytes']
 for n,v in f['guard_log_pins'].items():assert sha(dd/n)==v['sha256'] and (dd/n).stat().st_size==v['bytes']
 rows=c['completed_compiler_invocations'];assert [x['index'] for x in rows]==list(range(start,start+count))
 for row in rows:
  i=row['index'];q=row['receipt'];assert q==js(ST/f'{i:04d}.json') and row['receipt_sha256']==sha(ST/f'{i:04d}.json')
  for k,v in plan[i].items():assert q[k]==v,(i,k)
  assert sha(q['source'])==q['source_sha256'] and q['exit_code']==q['compiler_exit_code']==0
  assert q['runner_sha256']==PINS[str(S/'build_external_serial.py')] and q['resource_control']['helper_sha256']==PINS[str(S/'serial_compile.py')]
  expected=[str(Path('/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin/lean')),'-Dpp.unicode.fun=true','-DautoImplicit=false','-DmaxSynthPendingDepth=3','-j','1','-s','8192','-R',q['repo'],'-o',q['target'],q['source']]
  if not q['module'].startswith('Mathlib.'):expected=expected[:1]+expected[4:]
  assert q['command']==expected
  target=Path(q['target']);family={str(target),str(target)+'.private',str(target)+'.server',str(target.with_suffix('.ir')),str(target.with_suffix('.ir.sig'))};assert set(q['artifacts'])==family
  for p,h in q['artifacts'].items():assert sha(p)==h,p
  for n in ['stdout','stderr']:
   p=ST/f'{i:04d}.{n}';assert sha(p)==q[n+'_sha256']==row[n]['sha256'] and p.stat().st_size==row[n]['bytes'] and p.read_bytes()==row[n]['content_utf8'].encode()
 terminal=json.loads((out/'stdout').read_text().splitlines()[-1]);assert terminal==dict(status='BATCH_COMPLETE',freshly_compiled=count,authenticated_reuse=start,planned=3591,complete=False)
 m=sample(batch);assert not m['active_processes'] and not m['pause']
 result=dict(schema='astra_rust_lane_explicit_closed_batch_v2',observed_utc=m['observed_utc'],batch=batch,guard_sha256=sha(out/'RECEIPT.json'),capture_sha256=sha(out/'MODULE-RECEIPTS.json'),finish_sha256=sha(dd/'FINISH.json'),prebatch_sha256=sha(out/'PRE-BATCH-STATE.json'),guard_elapsed_seconds=g['elapsed_seconds'],guard_child_peak_rss=g['child_peak_rss_bytes'],fresh_indices=list(range(start,start+count)),fresh_artifacts_reauthenticated=count*5,source_log_receipt_command_reauthenticated=True,recorded_authenticated_reuse=start,guard_process_os_exit=f['guard_process_exit_code'],source_pins=PINS,final_monitor=m,next_index=start+count,next_module=plan[start+count]['module'],original042_057_059_outer_guard='UNKNOWN',no_repair_or_retry=True)
 save(E/f'RUST-LANE-{batch:03d}-CLOSED.json',result);return result
if __name__=='__main__':
 action=sys.argv[1];batch=int(sys.argv[2])
 if action=='sample': x=sample(batch)
 elif action=='closed':x=closed(batch,int(sys.argv[3]),int(sys.argv[4]))
 elif action=='preflight':
  pins();start=int(sys.argv[3]);x=sample(batch);assert not x['active_processes'] and not x['pause'];assert x['cgroup_bytes']<4*1024**3 and x['disk_free']>8*1024**3
  assert sorted(int(p.stem) for p in ST.glob('[0-9][0-9][0-9][0-9].json'))==list(range(start));assert not(E/f'external-batch-{batch:03d}').exists() and not(D/'evidence'/f'production-{batch:03d}').exists();x.update(expected_start=start,source_pins=PINS,monitor_script_sha256=sha(__file__));save(E/f'RUST-LANE-{batch:03d}-PREFLIGHT.json',x)
 else:raise ValueError(action)
 print(json.dumps(x))
