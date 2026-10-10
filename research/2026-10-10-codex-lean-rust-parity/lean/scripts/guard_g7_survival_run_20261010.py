#!/usr/bin/env python3
"""Serial outer resource monitor; it does not change the frozen Lean builder.

Contributor: Codex / lean_integration_successor, 2026-10-10.
The dated 2GiB scratch policy supersedes only our earlier storage plan. Normal
4GiB/180s and connected 6GiB/300s compiler policies remain unchanged.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def sha(path):
    with Path(path).open('rb') as stream:
        h = hashlib.sha256()
        for block in iter(lambda: stream.read(2**20), b''):
            h.update(block)
    return h.hexdigest()


def save(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + '\n')


def allocated(roots):
    seen, total = set(), 0
    for root in roots:
        for directory, dirs, files in os.walk(root):
            for path in [Path(directory), *(Path(directory) / n for n in files)]:
                try:
                    st = path.lstat()
                except FileNotFoundError:
                    continue
                key = (st.st_dev, st.st_ino)
                if key not in seen:
                    seen.add(key)
                    total += st.st_blocks * 512
    return total


def memory():
    values = dict(line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())
    chosen = {k: int(values[k]) for k in ['anon', 'shmem', 'kernel']}
    chosen['nonreclaimable_estimate'] = sum(chosen.values())
    chosen['memory_current_informational_only'] = int(Path('/sys/fs/cgroup/memory.current').read_text())
    return chosen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('workspace', type=Path)
    parser.add_argument('--phase', required=True, choices=['primary', 'secondary', 'union1503', 'union1504'])
    args = parser.parse_args()
    work = args.workspace.resolve(strict=True)
    config_path = work / 'RESOURCE-AND-RUN-PLAN.json'
    config = json.loads(config_path.read_bytes())
    assert sha(Path(__file__)) == config['monitor_sha256']
    assert sha(work / 'PREPARATION.json') == config['preparation_sha256']
    assert sha(work / 'DEPENDENCY-GRAPH.json') == config['graph_sha256']
    phase = config['phases'][args.phase]
    for required in phase['requires']:
        receipt = json.loads((work / 'guard-receipts' / (required + '.json')).read_bytes())
        assert receipt['status'] == 'PASS_UNCHANGED_BUILDER_EXIT_ZERO' and receipt['exit_code'] == 0
    receipt_path = work / 'guard-receipts' / (args.phase + '.json')
    assert not receipt_path.exists(), 'A phase may be executed only once in this dated context'
    assert not (work / 'ACTIVE-GUARDED-PROCESS.json').exists(), 'Serial scheduler marker exists'
    initial_memory = memory()
    initial_allocation = allocated(config['allocation_roots'])
    assert initial_memory['nonreclaimable_estimate'] < config['memory_abort_bytes']
    assert initial_allocation < config['scratch_abort_bytes']
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out = work / 'guard-runs' / (args.phase + '-' + stamp)
    out.mkdir(parents=True)
    command = [config['python'], config['launcher'], str(work), '--target', phase['target']]
    env = dict(os.environ, CONNECTED_LEAN_BIN=config['lean_bin'], CONNECTED_MATHLIB=config['mathlib'])
    (work / 'guard-receipts').mkdir(exist_ok=True)
    with (out / 'stdout.txt').open('wb') as stdout, (out / 'stderr.txt').open('wb') as stderr:
        child = subprocess.Popen(command, stdout=stdout, stderr=stderr, env=env, start_new_session=True)
        save(work / 'ACTIVE-GUARDED-PROCESS.json', {'pid': child.pid, 'phase': args.phase, 'output': str(out)})
        reason = None
        started = time.monotonic()
        peak_mem = initial_memory['nonreclaimable_estimate']
        peak_alloc = initial_allocation
        last_alloc = initial_allocation
        next_allocation_check = started
        with (out / 'resource-samples.jsonl').open('a') as samples:
            while child.poll() is None:
                current = memory()
                now = time.monotonic()
                if now >= next_allocation_check:
                    last_alloc = allocated(config['allocation_roots'])
                    next_allocation_check = now + 2
                peak_mem = max(peak_mem, current['nonreclaimable_estimate'])
                peak_alloc = max(peak_alloc, last_alloc)
                samples.write(json.dumps({'elapsed_seconds': round(now - started, 3), **current,
                                          'distinct_inode_allocated_bytes': last_alloc}) + '\n')
                samples.flush()
                if current['nonreclaimable_estimate'] >= config['memory_abort_bytes']:
                    reason = 'NONRECLAIMABLE_MEMORY_GUARD'
                elif last_alloc >= config['scratch_abort_bytes']:
                    reason = 'SCRATCH_GUARD_WITH_TRANSIENT_HEADROOM'
                if reason:
                    os.killpg(child.pid, signal.SIGTERM)
                    try:
                        child.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(child.pid, signal.SIGKILL)
                        child.wait()
                    break
                time.sleep(0.5)
        rc = child.wait()
    final_memory = memory()
    final_allocation = allocated(config['allocation_roots'])
    result = {'status': 'PASS_UNCHANGED_BUILDER_EXIT_ZERO' if rc == 0 and reason is None else 'PRESERVED_FAILED_OR_RESOURCE_ABORTED_RUN',
              'phase': args.phase, 'target': phase['target'], 'command': command, 'exit_code': rc,
              'abort_reason': reason, 'output': str(out), 'config_path': str(config_path),
              'config_sha256': sha(config_path), 'monitor_sha256': sha(Path(__file__)),
              'initial_memory': initial_memory, 'final_memory': final_memory,
              'peak_nonreclaimable_estimate_bytes': peak_mem,
              'initial_distinct_inode_allocation_bytes': initial_allocation,
              'peak_distinct_inode_allocation_bytes': max(peak_alloc, final_allocation),
              'final_distinct_inode_allocation_bytes': final_allocation,
              'resource_caps_kernel_flags_core_or_audit_changed': False,
              'stdout_sha256': sha(out / 'stdout.txt'), 'stderr_sha256': sha(out / 'stderr.txt')}
    save(out / 'RECEIPT.json', result)
    save(receipt_path, result)
    (work / 'ACTIVE-GUARDED-PROCESS.json').unlink()
    print(json.dumps(result))
    raise SystemExit(0 if result['status'].startswith('PASS_') else 1)


if __name__ == '__main__':
    main()
