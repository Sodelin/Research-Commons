#!/usr/bin/env python3
"""080-082 readback only; reuse the exact reviewed checker without changing frozen monitors."""
import hashlib, json, os, sys
from pathlib import Path

ROOT = Path('/workspace/Research-Commons')
EVIDENCE = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z/evidence'
PROVIDER = EVIDENCE / 'RUST-MONITOR-074-076-REPAIRED.py'
PIN = 'e0ae5d4f5ed0b4305a4045e7c7e8026f6ac07980be15441dde5d7adeb73a7e61'
body = PROVIDER.read_bytes()
if hashlib.sha256(body).hexdigest() != PIN:
    raise ValueError('reviewed readback provider changed')
ns = dict(__name__='astra_reviewed_readback_080_082', __file__=str(PROVIDER))
exec(compile(body, str(PROVIDER), 'exec'), ns)
ns['MON'] = EVIDENCE / 'RUST-LANE-MONITOR-080-082.jsonl'
old_save = ns['save']
def save(path, value):
    value = dict(value, executed_checker_provider_sha256=PIN,
        monitor_wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        readback_attribution='Rust lane independent 079 handoff and 080-082 explicit compiler ownership.')
    old_save(path, value)
ns['save'] = save
action = sys.argv[1]
batch = int(sys.argv[2])
if action == 'closed':
    start, count = int(sys.argv[3]), int(sys.argv[4])
    if (batch, start, count) not in ((79,3261,16),(80,3277,8),(81,3285,8),(82,3293,8)):
        raise ValueError('outside explicit handoff')
    result = ns['closed'](batch, start, count)
elif action == 'sample':
    if batch not in (79,80,81,82):
        raise ValueError('outside explicit handoff')
    result = ns['sample'](batch)
elif action == 'preflight':
    start = int(sys.argv[3])
    if (batch,start) not in ((80,3277),(81,3285),(82,3293)):
        raise ValueError('outside explicit handoff')
    ns['pins']()
    result = ns['sample'](batch)
    assert not result['active_processes'] and not result['pause']
    assert result['cgroup_bytes'] < 4*1024**3 and result['disk_free'] > 8*1024**3
    assert sorted(int(p.stem) for p in ns['ST'].glob('[0-9][0-9][0-9][0-9].json')) == list(range(start))
    assert not (ns['E']/f'external-batch-{batch:03d}').exists()
    assert not (ns['D']/'evidence'/f'production-{batch:03d}').exists()
    result.update(expected_start=start, fresh_budget=8, source_pins=ns['PINS'])
    save(ns['E']/f'RUST-LANE-{batch:03d}-PREFLIGHT.json', result)
else:
    raise ValueError('readback/preflight only; no launch, stop, repair or retry')
print(json.dumps(result))
