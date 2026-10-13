#!/usr/bin/env python3
"""Sample one unchanged selected Lean invocation under an external guard."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'2026-10-13-astra-unified-solver-0645z'))
from build_mathlib_serial import setup,sha,artifacts,LEAN_SHA,PIN

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--index',type=int,required=True)
p.add_argument('--mathlib-root',type=Path,required=True)
p.add_argument('--lean-bin',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--synchronous',action='store_true',help='Disable asynchronous theorem elaboration without changing source.')
p.add_argument('--advise-input-cache',action='store_true',help='Advisory release of clean completed input-object pages, without changing files or limits.')
a=p.parse_args()
repos,pins,env=setup(a.mathlib_root,a.lean_bin)
plan=json.loads((HERE/'EXTERNAL-PLAN.json').read_text())
row=plan['modules'][a.index]
if sha(Path(row['source']))!=row['source_sha256']:raise ValueError('selected source changed')
if plan['compiler_sha256']!=LEAN_SHA or plan['mathlib_pin']!=PIN or plan['dependencies']!=pins:
    raise ValueError('selected compiler/dependency context differs')
a.out.mkdir(parents=True,exist_ok=False)
target=Path(row['target'])
if artifacts(target):raise ValueError('diagnostic target already contains artifacts; preserve and inspect first')
command=[str(a.lean_bin/'lean'),'-j','1','-s','8192','-R',row['repo'],'-o',str(target),row['source']]
if a.synchronous:command.insert(1,'-DElab.async=false')
source_copy=a.out/'source.lean';source_copy.write_bytes(Path(row['source']).read_bytes())
input_paths=[]
if a.advise_input_cache:
    input_paths=[path for path in (a.lean_bin.parent/'lib').rglob('*') if path.is_file()]
    for previous in plan['modules'][:a.index]:
        previous_target=Path(previous['target'])
        input_paths.extend(path for suffix in ['.olean','.olean.private','.olean.server','.ir','.ir.sig']
                           if (path:=previous_target.with_suffix(suffix)).is_file())
    input_paths=sorted(set(input_paths))
    if target in input_paths:raise ValueError('active output must not be a cache-advice input')
    (a.out/'CACHE-INPUTS.json').write_text(json.dumps(list(map(str,input_paths)),indent=2)+'\n')
base=dict(selected=row,command=command,runner_sha256=sha(Path(__file__)),
          compiler_sha256=LEAN_SHA,mathlib_pin=PIN,
          environment={key:env[key] for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_NUM_THREADS',
                       'LEAN_STACK_SIZE_KB','LEAN_IMPORT_WORKERS','MIMALLOC_ARENA_RESERVE','RAYON_NUM_THREADS']},
          cgroup_events_before=Path('/sys/fs/cgroup/memory.events').read_text())
base['input_cache_advice']=dict(enabled=a.advise_input_cache,threshold_bytes=3*1024**3,
                              minimum_interval_seconds=1,files_changed=False,
                              input_inventory_sha256=sha(a.out/'CACHE-INPUTS.json') if input_paths else None)
(a.out/'INVOCATION.json').write_text(json.dumps(base,indent=2)+'\n')
started=time.monotonic();samples=[];last_advice=-10
with (a.out/'stdout').open('xb') as out,(a.out/'stderr').open('xb') as err,(a.out/'samples.jsonl').open('x') as log:
    child=subprocess.Popen(command,cwd=row['repo'],env=env,stdout=out,stderr=err)
    while child.poll() is None:
        sample=dict(seconds=time.monotonic()-started,cgroup_bytes=int(Path('/sys/fs/cgroup/memory.current').read_text()))
        try:
            status=dict(line.split(':',1) for line in (Path('/proc')/str(child.pid)/'status').read_text().splitlines() if ':' in line)
            for key in ['VmPeak','VmSize','VmRSS','VmHWM']:
                if key in status:sample[key+'_bytes']=int(status[key].split()[0])*1024
            sample['threads']=int(status['Threads'])
            if not (a.out/'child-maps.txt').exists() and sample['seconds']>4:
                (a.out/'child-maps.txt').write_text((Path('/proc')/str(child.pid)/'maps').read_text())
                (a.out/'child-smaps-rollup.txt').write_text((Path('/proc')/str(child.pid)/'smaps_rollup').read_text())
        except FileNotFoundError:pass
        if input_paths and sample['cgroup_bytes']>3*1024**3 and sample['seconds']-last_advice>=1:
            before=sample['cgroup_bytes'];advice_start=time.monotonic()
            for path in input_paths:
                with path.open('rb') as handle:
                    os.fsync(handle.fileno())
                    os.posix_fadvise(handle.fileno(),0,0,os.POSIX_FADV_DONTNEED)
            last_advice=time.monotonic()-started
            sample['input_cache_advice']=dict(before_cgroup_bytes=before,
                after_cgroup_bytes=int(Path('/sys/fs/cgroup/memory.current').read_text()),
                seconds=time.monotonic()-advice_start,files=len(input_paths))
        samples.append(sample);log.write(json.dumps(sample)+'\n');log.flush()
        time.sleep(0.02)
    code=child.wait()
result=dict(base,exit_code=code,seconds=time.monotonic()-started,artifacts=artifacts(target),
            stdout_sha256=sha(a.out/'stdout'),stderr_sha256=sha(a.out/'stderr'),
            sampled_peaks={key:max((r.get(key,0) for r in samples),default=0)
                           for key in ['VmPeak_bytes','VmSize_bytes','VmRSS_bytes','VmHWM_bytes','cgroup_bytes','threads']},
            cgroup_events_after=Path('/sys/fs/cgroup/memory.events').read_text())
(a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(module=row['module'],exit_code=code,seconds=result['seconds'],
                      sampled_peaks=result['sampled_peaks'])),flush=True)
raise SystemExit(code)
