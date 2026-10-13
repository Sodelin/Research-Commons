"""One compiler child with bounded, advisory input-cache housekeeping.

The external guard owns physical/virtual/time limits. This helper never changes
those limits, source/object bytes, global settings, or active output files.
Callers authenticate the completed input objects before passing their paths.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

LOADED_SHA=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
THRESHOLD=3*1024**3


def toolchain_inputs(lean_bin):
    root=(lean_bin.parent/'lib').resolve()
    result=set()
    for path in root.rglob('*'):
        if path.is_file():
            if not path.resolve().is_relative_to(root):
                raise ValueError('toolchain input symlink escapes authenticated root')
            result.add(str(path))
    return result


def compile_one(command,*,cwd,env,stdout,stderr,input_files,target,index,module):
    inputs=sorted(set(map(str,input_files)))
    forbidden={str(target.with_suffix(s)) for s in
               ['.olean','.olean.private','.olean.server','.ir','.ir.sig']}
    if forbidden.intersection(inputs):
        raise ValueError('active outputs included in cache-advice input inventory')
    child_env=env.copy();child_env['MALLOC_ARENA_MAX']='1'
    policy=dict(helper_sha256=LOADED_SHA,malloc_arena_max='1',
                input_inventory_sha256=hashlib.sha256(json.dumps(inputs).encode()).hexdigest(),
                input_files=len(inputs),threshold_bytes=THRESHOLD,
                minimum_advice_interval_seconds=1,sample_interval_seconds=0.1,
                sampler_pauses_during_advice=True,files_changed=False,
                system_settings_changed=False,outer_limits_changed=False)
    started=time.monotonic();last_advice=-10;advice_count=0;peaks={}
    def event(kind,**fields):
        print(json.dumps(dict(resource_event=kind,resource_index=index,
                              resource_module=module,**fields)),flush=True)
    event('COMPILER_RESOURCE_POLICY',policy=policy)
    with stdout.open('xb') as out,stderr.open('xb') as err:
        child=subprocess.Popen(command,cwd=cwd,env=child_env,stdout=out,stderr=err)
        try:
            while child.poll() is None:
                now=time.monotonic()-started
                sample={'cgroup_bytes':int(Path('/sys/fs/cgroup/memory.current').read_text())}
                try:
                    status=dict(line.split(':',1) for line in
                                (Path('/proc')/str(child.pid)/'status').read_text().splitlines() if ':' in line)
                    for key in ['VmPeak','VmRSS','VmHWM']:
                        if key in status:sample[key+'_bytes']=int(status[key].split()[0])*1024
                except FileNotFoundError:pass
                for key,value in sample.items():peaks[key]=max(value,peaks.get(key,0))
                if sample['cgroup_bytes']>THRESHOLD and now-last_advice>=1:
                    event('INPUT_CACHE_ADVICE_BEGIN',seconds=now,sample=sample)
                    advice_start=time.monotonic()
                    for path in inputs:
                        with open(path,'rb') as handle:
                            os.fsync(handle.fileno())
                            os.posix_fadvise(handle.fileno(),0,0,os.POSIX_FADV_DONTNEED)
                    last_advice=time.monotonic()-started;advice_count+=1
                    event('INPUT_CACHE_ADVICE_END',seconds=last_advice,
                          elapsed_seconds=time.monotonic()-advice_start,
                          after_cgroup_bytes=int(Path('/sys/fs/cgroup/memory.current').read_text()))
                time.sleep(0.1)
        except BaseException:
            event('RESOURCE_HELPER_ABORT',seconds=time.monotonic()-started)
            if child.poll() is None:
                child.terminate()
                try:child.wait(timeout=5)
                except subprocess.TimeoutExpired:child.kill();child.wait()
            raise
        code=child.wait()
    return code,dict(policy,completed_advice_sweeps=advice_count,
                     sampled_peaks=peaks,seconds=time.monotonic()-started)
