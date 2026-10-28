#!/usr/bin/env python3
"""Bound one process group; preserve command, resources, output and failure.

Linux/cloud only. Does not delete work, alter a toolchain, or retry a build.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import subprocess
import time

GIB = 1024**3


def state(path):
    mem = dict(row.split(':', 1) for row in Path('/proc/meminfo').read_text().splitlines())
    return dict(disk_free=shutil.disk_usage(path).free,
                ram_available=int(mem['MemAvailable'].split()[0]) * 1024,
                cgroup_memory=int(Path('/sys/fs/cgroup/memory.current').read_text()))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--cwd', type=Path, required=True)
    p.add_argument('--wall', type=int, default=180)
    p.add_argument('--cpu', type=int, default=120)
    p.add_argument('--memory-mib', type=int, default=3072)
    p.add_argument('--file-mib', type=int, default=1024)
    p.add_argument('command', nargs=argparse.REMAINDER)
    a = p.parse_args()
    command = a.command[1:] if a.command[:1] == ['--'] else a.command
    if not command:
        p.error('a command is required')
    a.out.mkdir(parents=True, exist_ok=False)
    def limits():
        for key, cap in [(resource.RLIMIT_AS, a.memory_mib * 1024**2),
                         (resource.RLIMIT_CPU, a.cpu),
                         (resource.RLIMIT_FSIZE, a.file_mib * 1024**2),
                         (resource.RLIMIT_CORE, 0)]:
            resource.setrlimit(key, (cap, cap))
    def pressure(s):
        return ('disk_floor' if s['disk_free'] < 8*GIB else
                'ram_floor' if s['ram_available'] < GIB else
                'cgroup_pressure' if s['cgroup_memory'] >= 4*GIB else None)
    started = time.monotonic()
    receipt = dict(schema='astra_serial_execution_v1', command=command,
                   cwd=str(a.cwd.resolve()), started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   limits=dict(cpu_seconds=a.cpu, wall_seconds=a.wall,
                               address_space_bytes=a.memory_mib*1024**2, file_bytes=a.file_mib*1024**2,
                               disk_floor=8*GIB, ram_floor=GIB, cgroup_stop=4*GIB))
    samples = []
    child = None
    stop = None
    try:
        with (a.out/'stdout').open('xb') as out, (a.out/'stderr').open('xb') as err:
            initial = state(a.out)
            samples.append(dict(seconds=0, **initial))
            stop = pressure(initial)
            if not stop:
                child = subprocess.Popen(command, cwd=a.cwd, stdout=out, stderr=err,
                                         start_new_session=True, preexec_fn=limits)
                while child.poll() is None:
                    current = state(a.out)
                    elapsed = time.monotonic()-started
                    samples.append(dict(seconds=elapsed, **current))
                    stop = pressure(current) or ('wall_limit' if elapsed > a.wall else None)
                    if stop:
                        os.killpg(child.pid, signal.SIGTERM)
                        try:
                            child.wait(timeout=2)
                        except subprocess.TimeoutExpired:
                            pass
                        # A parent can exit before its worker; always kill the
                        # remaining group after stopping, not only the parent.
                        try:
                            os.killpg(child.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        child.wait()
                        break
                    time.sleep(0.5)
    except BaseException as e:
        receipt['error'] = {'type': type(e).__name__, 'message': str(e)}
        raise
    finally:
        if child:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
        receipt.update(exit_code=None if child is None else child.returncode,
                       stop=stop, elapsed_seconds=time.monotonic()-started, samples=samples,
                       child_peak_rss_bytes=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss*1024,
                       runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
        receipt['outputs'] = {name: dict(bytes=(a.out/name).stat().st_size,
                            sha256=hashlib.sha256((a.out/name).read_bytes()).hexdigest())
                              for name in ('stdout', 'stderr')}
        (a.out/'RECEIPT.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k != 'samples'}))
    return 0 if child and child.returncode == 0 and not stop else 1


if __name__ == '__main__':
    raise SystemExit(main())
