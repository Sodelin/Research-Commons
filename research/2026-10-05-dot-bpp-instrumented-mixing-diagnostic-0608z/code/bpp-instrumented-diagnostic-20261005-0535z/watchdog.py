"""Resource monitor for one isolated subprocess group, retaining partial evidence.
Aggregate logical file bytes include nested files, inputs, logs and receipts.
This is a polling stop rule, not an OS filesystem quota; overshoot is recorded.
"""
import os,signal,stat,subprocess,time
from pathlib import Path

def tree_bytes(folder):
    total=0
    for root,dirs,files in os.walk(folder,followlinks=False):
        for name in dirs+files:
            path=Path(root)/name
            try:s=path.lstat()
            except FileNotFoundError:continue
            if stat.S_ISLNK(s.st_mode):raise ValueError("symlink output is forbidden in monitored attempt")
            if stat.S_ISREG(s.st_mode):total+=s.st_size
    return total

def terminate_group(proc,grace=1.0):
    if proc is None:return
    try:os.killpg(proc.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    deadline=time.monotonic()+grace
    while time.monotonic()<deadline:
        proc.poll()
        try:os.killpg(proc.pid,0)
        except ProcessLookupError:break
        time.sleep(.02)
    try:os.killpg(proc.pid,signal.SIGKILL)
    except ProcessLookupError:pass
    try:proc.wait(timeout=5)
    except subprocess.TimeoutExpired:raise RuntimeError('isolated process did not exit after SIGKILL')

def monitor(proc,folder,wall_seconds,size_limit_bytes,receipt_reserve_bytes=1048576,poll_seconds=.05):
    if not(0<=receipt_reserve_bytes<size_limit_bytes) or wall_seconds<=0 or poll_seconds<=0:raise ValueError('invalid watchdog limits')
    start=time.monotonic();peak=0;trigger=None
    while True:
        size=tree_bytes(folder);peak=max(peak,size)
        if size>=size_limit_bytes-receipt_reserve_bytes:
            trigger='AGGREGATE_OUTPUT_LIMIT';terminate_group(proc);break
        rc=proc.poll()
        if rc is not None:break
        if time.monotonic()-start>=wall_seconds:
            trigger='RESOURCE_TIME_LIMIT';terminate_group(proc);break
        time.sleep(poll_seconds)
    peak=max(peak,tree_bytes(folder))
    # Clean up any descendants even if the direct engine parent exited first.
    terminate_group(proc)
    peak=max(peak,tree_bytes(folder))
    return {'status':trigger or ('EXECUTION_EXIT_ZERO' if proc.returncode==0 else 'EXECUTION_FAILED'),'exit_code':proc.returncode,'monitor_seconds':time.monotonic()-start,'aggregate_byte_limit':size_limit_bytes,'receipt_reserve_bytes':receipt_reserve_bytes,'stop_threshold_bytes':size_limit_bytes-receipt_reserve_bytes,'peak_observed_bytes_before_final_receipt':peak,'threshold_overshoot_observed_bytes':max(0,peak-(size_limit_bytes-receipt_reserve_bytes)),'cap_overshoot_observed_bytes':max(0,peak-size_limit_bytes),'poll_seconds':poll_seconds,'hard_filesystem_quota_claimed':False,'process_group_cleanup_performed':True,'direct_child_reaped':proc.poll() is not None,'counting_rule':'logical regular-file bytes, recursively including inputs/logs/receipts; symlinks forbidden'}
