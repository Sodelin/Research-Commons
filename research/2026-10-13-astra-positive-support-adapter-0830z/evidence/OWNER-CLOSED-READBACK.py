#!/usr/bin/env python3
"""Reuse a pinned read-only checker, with separate owner-labelled outputs.

No compiler, launcher, signal or repair is invoked. The final external-plan
boundary needs a separate checker because the inherited function requires a
next module and complete=False. Historical Rust monitor bytes stay unchanged.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PROVIDER = HERE / 'RUST-MONITOR-074-076-REPAIRED.py'
PROVIDER_SHA = 'e0ae5d4f5ed0b4305a4045e7c7e8026f6ac07980be15441dde5d7adeb73a7e61'
assert hashlib.sha256(PROVIDER.read_bytes()).hexdigest() == PROVIDER_SHA
batch, start, count = map(int, sys.argv[1:])
assert 77 <= batch <= 999 and 1 <= count <= 64 and start + count < 3591
spec = importlib.util.spec_from_file_location('pinned_closed_readback', PROVIDER)
provider = importlib.util.module_from_spec(spec)
spec.loader.exec_module(provider)
provider.MON = HERE / f'OWNER-MONITOR-{batch:03d}.jsonl'
assert not provider.MON.exists()
original_save = provider.save

def owner_save(path, result):
    assert path == HERE / f'RUST-LANE-{batch:03d}-CLOSED.json'
    result['schema'] = 'astra_owner_closed_batch_readback_v1'
    result['executed_checker_provider_sha256'] = PROVIDER_SHA
    result['owner_wrapper_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result['readback_attribution'] = 'Lean integration owner; reused unchanged Rust-lane checker function.'
    original_save(HERE / f'OWNER-{batch:03d}-CLOSED.json', result)

provider.save = owner_save
result = provider.closed(batch, start, count)
print(json.dumps({key: result[key] for key in ['batch', 'guard_sha256',
    'capture_sha256', 'guard_elapsed_seconds', 'fresh_artifacts_reauthenticated',
    'next_index', 'next_module', 'guard_process_os_exit']}))
