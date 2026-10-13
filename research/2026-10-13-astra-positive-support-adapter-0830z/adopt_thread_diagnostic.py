#!/usr/bin/env python3
"""Adopt one authenticated successful diagnostic; archive the failed ledger bytes.

No compiler is invoked. This does not rewrite either historical guard receipt.
"""
import datetime
import json
from pathlib import Path

import build_external_serial as external
from recover_batch_042 import process_snapshot

HERE = Path(__file__).resolve().parent
STATE = Path('/workspace/scratch/astra-support-external-0840')
DIAGNOSTIC = HERE / 'evidence/thread-headroom-2860-v2'
FAILED_SHA = '05d682973501c3af2a74bd4d6b8b3015741d7ca32d58cbcb258b273992dd456d'
RESULT_SHA = '4f4a6d8932f405979d02f02b766d85063686875a17ec40e57a5f7ec195110e8f'
GUARD_SHA = '851ba3fc78c41c9f3181857d89add49ea1725fa925c6d3152fafd71d34181dce'
RUNNER_SHA = '2648d7e48979c1c241fe2563b7ea40c98034a38d2a0cbe15b535718ac5c5baf9'


def main():
    process_snapshot()
    if (HERE / 'PAUSE-BUILDS').exists():
        raise ValueError('coordinator pause is active')
    source = DIAGNOSTIC / 'compilation'
    for path, digest in [(DIAGNOSTIC / 'RECEIPT.json', GUARD_SHA),
                         (source / 'RESULT.json', RESULT_SHA),
                         (source / 'runner.py', RUNNER_SHA),
                         (STATE / '2860.json', FAILED_SHA)]:
        if external.sha(path) != digest:
            raise ValueError('pinned diagnostic or original failure differs: ' + str(path))
    result = json.loads((source / 'RESULT.json').read_text())
    guard = json.loads((DIAGNOSTIC / 'RECEIPT.json').read_text())
    failed = json.loads((STATE / '2860.json').read_text())
    if (result['exit_code'] != 0 or result['compiler_exit_code'] != 0
            or guard['exit_code'] != 0 or guard['stop'] is not None
            or result['monitor_errors'] or result['runner_sha256'] != RUNNER_SHA
            or guard['runner_sha256'] != external.pins['guard.py']):
        raise ValueError('diagnostic was not completely successful under the frozen guard')
    if guard['limits'] != dict(cpu_seconds=120, wall_seconds=180,
            address_space_bytes=6*1024**3, file_bytes=1024**3,
            disk_floor=8*1024**3, ram_floor=1024**3, cgroup_stop=4*1024**3):
        raise ValueError('diagnostic guard profile differs')
    if result['command'] != failed['command']:
        raise ValueError('compiler invocation changed')
    for name in ['stdout', 'stderr']:
        if (external.sha(source / name) != result[name + '_sha256']
                or external.sha(DIAGNOSTIC / name) != guard['outputs'][name]['sha256']
                or external.sha(STATE / ('2860.' + name)) != failed[name + '_sha256']):
            raise ValueError('successful or original failed log changed')
    row = result['selected']
    if (any(failed[key] != value for key, value in row.items())
            or external.sha(Path(row['source'])) != row['source_sha256']
            or external.sha(source / 'source.lean') != row['source_sha256']
            or external.artifacts(Path(row['target'])) != result['artifacts']
            or not result['artifacts']):
        raise ValueError('source selection or compiled artifacts differ')
    prefix_path = source / 'AUTHENTICATED-PREFIX.json'
    if external.sha(prefix_path) != result['authenticated_prefix_sha256']:
        raise ValueError('diagnostic prefix ledger changed')
    prefix = json.loads(prefix_path.read_text())
    if [row['index'] for row in prefix] != list(range(2860)):
        raise ValueError('diagnostic prefix ledger is incomplete')
    for previous in prefix:
        if external.sha(STATE / f"{previous['index']:04d}.json") != previous['receipt_sha256']:
            raise ValueError('earlier authenticated receipt changed')
    archive = STATE / 'preserved-failure-2860-batch054'
    if archive.exists() or (HERE / 'evidence/THREAD-HEADROOM-2860-ADOPTION.json').exists():
        raise ValueError('adoption already started; inspect preserved evidence before recovery')
    candidate = dict(**row, command=result['command'], exit_code=0, compiler_exit_code=0,
        runner_sha256=RUNNER_SHA, execution='FRESH_SOURCE_COMPILE_6GIB_VIRTUAL_DIAGNOSTIC',
        seconds=result['seconds'], artifacts=result['artifacts'],
        stdout_sha256=result['stdout_sha256'], stderr_sha256=result['stderr_sha256'],
        environment=dict(result['environment'], **result['helper_child_environment']),
        resource_control=result['resource_control'], diagnostic_result_sha256=RESULT_SHA,
        diagnostic_guard_sha256=GUARD_SHA, original_failed_receipt_sha256=FAILED_SHA,
        preserved_original_failure=str(archive), original_batch054_guard_exit_code=1,
        prior_diagnostic_v1_exit_code=2)
    archive.mkdir()
    for name in ['2860.json', '2860.stdout', '2860.stderr']:
        (STATE / name).rename(archive / name)
    for name in ['stdout', 'stderr']:
        with (STATE / ('2860.' + name)).open('xb') as stream:
            stream.write((source / name).read_bytes())
    with (STATE / '2860.json').open('x') as stream:
        json.dump(candidate, stream, indent=2)
        stream.write('\n')
    record = dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        action='ADOPT_AUTHENTICATED_DIAGNOSTIC_OBJECTS_NO_COMPILATION',
        runner_sha256=external.sha(Path(__file__)), result_sha256=RESULT_SHA,
        guard_sha256=GUARD_SHA, original_failed_receipt_sha256=FAILED_SHA,
        archived_receipt_sha256=external.sha(archive / '2860.json'),
        adopted_receipt_sha256=external.sha(STATE / '2860.json'),
        receipt=candidate, original_batch054_unchanged=True,
        original_batch042_outer_guard='UNKNOWN', cause_of_thread_failure='UNKNOWN')
    if record['archived_receipt_sha256'] != FAILED_SHA:
        raise ValueError('archived original failure differs')
    with (HERE / 'evidence/THREAD-HEADROOM-2860-ADOPTION.json').open('x') as stream:
        json.dump(record, stream, indent=2)
        stream.write('\n')
    print(json.dumps({key: value for key, value in record.items() if key != 'receipt'}))


if __name__ == '__main__':
    main()
