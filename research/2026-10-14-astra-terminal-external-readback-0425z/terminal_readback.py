#!/usr/bin/env python3
"""Read back only an actual terminal external batch; never compile or launch.

The full prefix provenance export, owned provider compilation, and final
Lake/type/axiom audits are separate obligations. No historical guard is repaired.
"""
import hashlib
import json
from pathlib import Path
import sys
import types

HERE = Path(__file__).resolve().parent
EVIDENCE = Path('/workspace/Research-Commons/research/2026-10-13-astra-positive-support-adapter-0830z/evidence')
PROVIDER = HERE / 'terminal_provider.py'
PROVIDER_SHA = 'da2c51fd8a068208cc021c94bf274fc13255a9cc9643747f31c8c729bc80e005'
PIN_RECORD = EVIDENCE / 'RUST-LANE-070-CLOSED.json'
PIN_RECORD_SHA = '754f413e6765b139e17ffd1aef4d15903e37605162912aa3d59dfe239d27db68'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

batch, start, count = map(int, sys.argv[1:])
assert 77 <= batch <= 999 and 1 <= count <= 64 and start + count == 3591
provider_bytes = PROVIDER.read_bytes()
assert hashlib.sha256(provider_bytes).hexdigest() == PROVIDER_SHA
assert digest(PIN_RECORD) == PIN_RECORD_SHA
provider = types.ModuleType('pinned_terminal_readback')
provider.__file__ = str(PROVIDER)
exec(compile(provider_bytes, str(PROVIDER), 'exec'), provider.__dict__)
provider.MON = EVIDENCE / f'OWNER-TERMINAL-MONITOR-{batch:03d}.jsonl'
assert not provider.MON.exists()
output = EVIDENCE / f'OWNER-TERMINAL-{batch:03d}-CLOSED.json'
assert not output.exists()
original_save = provider.save

def owner_save(path, result):
    assert path == EVIDENCE / f'RUST-LANE-{batch:03d}-CLOSED.json'
    result['schema'] = 'astra_owner_terminal_batch_readback_v1'
    result['executed_checker_provider_sha256'] = PROVIDER_SHA
    result['owner_wrapper_sha256'] = digest(Path(__file__))
    result['pin_record_sha256'] = PIN_RECORD_SHA
    result['readback_attribution'] = 'Lean integration owner; terminal successor of pinned closed-batch checker.'
    result['terminal_builder_report_authenticated'] = True
    result['full_prefix_provenance_export_performed'] = False
    result['owned_provider_or_Lake_type_axiom_completion_claimed'] = False
    original_save(output, result)

provider.save = owner_save
result = provider.closed(batch, start, count)
print(json.dumps({key: result[key] for key in ['batch', 'guard_sha256',
    'capture_sha256', 'guard_elapsed_seconds', 'fresh_artifacts_reauthenticated',
    'next_index', 'next_module', 'guard_process_os_exit',
    'terminal_builder_report_authenticated', 'full_prefix_provenance_export_performed']}))
