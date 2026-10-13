#!/usr/bin/env python3
"""Authenticate recovered batch059 objects without launching a Lean compiler.

The original outer guard receipt is absent. This append-only readback cannot
recover its exit status, elapsed time, resource maxima, or reason for interruption.
Run under a NEW guard receipt, which certifies this readback only.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path

import build_external_serial as external
import capture_batch as capture
import serial_compile

HERE=Path(__file__).resolve().parent
BEGIN=2927
END=2959
# Snapshot first authenticated in this recovery at23:14UTC; no monitoring file
# or historical observation of the final059 completion is supplied. Original
# guard status, timing, maxima and interruption cause are not reconstructed.
SNAPSHOT_PINS={'evidence/ORCHESTRATOR-059.json': 'f48bd5bc0c2052445ebfd60bc3ba50bb1eaf934600881f4c2a6bdc628e30c61a', 'evidence/LEAN-LANE-059-PREFLIGHT.json': '3b765def64e87a0ad343fd63c11ba5914a4e67f64ca46a9d3cc6700826fb0ea1', 'evidence/external-batch-059/stdout': '688cad4b6dc37048c7c08adc247a0bebd875fdc55a5d310c9f55e15ddc3658af', 'evidence/external-batch-059/stderr': 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855', 'evidence/ORCHESTRATOR-058.json': 'e2fd49c13f7da05e998065df820ae12991d11ffc02fd9c7a5ab073cd2d4a17cc', 'evidence/external-batch-058/RECEIPT.json': 'b4f0857cf954a89de6321d62f124b0e12fed4f2bc53f61a61fd2b530967bb1d7', 'evidence/external-batch-058/MODULE-RECEIPTS.json': '642183c6e68ee9dd15bab9f2dd5599208a4fd73d2921cb4b1074c2e39d887fef'}


def save(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x') as stream:
        json.dump(value,stream,indent=2);stream.write('\n')


def copy(source,target,expected=None):
    digest=external.sha(source)
    if expected is not None and digest!=expected:
        raise ValueError('source identity changed before capture: '+str(source))
    target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as stream:stream.write(source.read_bytes())
    if external.sha(target)!=digest:raise ValueError('captured copy differs')
    return digest


def process_snapshot():
    names={'build_external_serial.py','run_external_batches.py','build_support.py',
           'run_provider_batches.py','audit_support_interface.py',
           'run_external_batches_6g.py','diagnose_thread_failure.py'}
    observed=[]
    for entry in Path('/proc').glob('[0-9]*'):
        try:
            status=dict(line.split(':',1) for line in (entry/'status').read_text().splitlines()
                        if ':' in line)
            args=[part.decode(errors='replace') for part in (entry/'cmdline').read_bytes().split(b'\0') if part]
            comm=(entry/'comm').read_text().strip()
            relevant=comm in {'lean','lake'} or any(Path(arg).name in names for arg in args)
            if relevant:
                row=dict(pid=int(entry.name),state=status['State'].strip(),comm=comm,args=args)
                observed.append(row)
                if not row['state'].startswith('Z'):
                    raise ValueError('active compiler or orchestration process: '+str(row))
        except (FileNotFoundError,ProcessLookupError):pass
    return observed


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['mathlib-root','lean-bin','state','out']:
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args()
    for name in ['mathlib_root','lean_bin','state','out']:
        setattr(args,name,getattr(args,name).resolve())
    if (HERE/'PAUSE-BUILDS').exists():raise ValueError('coordinator pause is active')
    args.out.mkdir(parents=True,exist_ok=False)
    start_processes=process_snapshot()
    batch=HERE/'evidence/external-batch-059'
    orchestrator=HERE/'evidence/ORCHESTRATOR-059.json'
    if (batch/'RECEIPT.json').exists() or (batch/'MODULE-RECEIPTS.json').exists():
        raise ValueError('original guard/capture state differs; investigate before recovery')
    for name,digest in SNAPSHOT_PINS.items():
        if external.sha(HERE/name)!=digest:raise ValueError('independent recovery snapshot changed: '+name)
    runner_pins=json.loads((HERE/'evidence/LEAN-LANE-059-PREFLIGHT.json').read_text())['runner_pins']
    if set(runner_pins)!={'run_external_batches_6g.py','build_external_serial.py',
                         'serial_compile.py','capture_batch.py'}:
        raise ValueError('retained preflight runner selection differs')
    for name,digest in runner_pins.items():
        if external.sha(HERE/name)!=digest:raise ValueError('retained preflight runner changed: '+name)
    if (external.LOADED_SHA!=runner_pins['build_external_serial.py']
            or serial_compile.LOADED_SHA!=runner_pins['serial_compile.py']
            or capture.LOADED_SHA!=runner_pins['capture_batch.py']):
        raise ValueError('loaded recovery authentication implementation differs')
    originals={str(path):external.sha(path) for path in [orchestrator,batch/'stdout',batch/'stderr']}
    for path in [orchestrator,HERE/'evidence/LEAN-LANE-059-PREFLIGHT.json',
                 HERE/'evidence/ORCHESTRATOR-058.json']:
        copy(path,args.out/'original'/path.name)
    for suffix in ['stdout','stderr']:copy(batch/suffix,args.out/'original/batch059'/suffix)
    copy(Path(__file__),args.out/'configuration/recover_batch_059.py')

    recorded=json.loads(orchestrator.read_text())
    if (recorded['first_batch']!=59 or recorded['requested_batches']!=1
            or recorded['batch_size']!=32 or recorded['pending_batch']['number']!=59
            or recorded['batches']!=[]):
        raise ValueError('original orchestration scope differs')
    if (recorded['runner_sha256']!=external.sha(HERE/'run_external_batches_6g.py')
            or recorded['capture_runner_sha256']!=capture.LOADED_SHA):
        raise ValueError('original orchestration/capture source pin differs')
    prior_record=json.loads((HERE/'evidence/ORCHESTRATOR-058.json').read_text())
    if (prior_record['first_batch']!=58 or prior_record['requested_batches']!=1
            or prior_record['batch_size']!=1 or prior_record.get('pending_batch') is not None
            or [row['number'] for row in prior_record['batches']]!=[58]):
        raise ValueError('prior one-module continuation scope differs')
    preflight=json.loads((HERE/'evidence/LEAN-LANE-059-PREFLIGHT.json').read_text())
    if (preflight['previous058_guard_sha256']!=external.sha(HERE/'evidence/external-batch-058/RECEIPT.json')
            or preflight['first_batch']!=59 or preflight['batches']!=1
            or preflight['fresh_budget']!=32 or preflight['next_index']!=BEGIN):
        raise ValueError('retained continuation preflight binding differs')
    for row in prior_record['batches']:
        directory=HERE/'evidence'/f"external-batch-{row['number']:03d}"
        guard=json.loads((directory/'RECEIPT.json').read_text())
        captured=json.loads((directory/'MODULE-RECEIPTS.json').read_text())
        if (row['exit_code']!=0 or guard['exit_code']!=0 or guard['stop'] is not None
                or external.sha(directory/'RECEIPT.json')!=row['receipt_sha256']):
            raise ValueError('preceding batch result differs')
        if (guard['runner_sha256']!=external.pins['guard.py']
                or guard['cwd']!=str(HERE.parent.parent)
                or guard['command']!=row['command'][row['command'].index('--')+1:]
                or guard['limits']!=dict(cpu_seconds=600,wall_seconds=900,
                    address_space_bytes=6*1024**3,file_bytes=1024**3,
                    disk_floor=8*1024**3,ram_floor=1024**3,cgroup_stop=4*1024**3)):
            raise ValueError('preceding guard binding or recorded limits differ')
        if (captured['capture_runner_sha256']!=capture.LOADED_SHA
                or captured['prebatch_inventory_sha256']!=external.sha(directory/'PRE-BATCH-STATE.json')):
            raise ValueError('preceding capture implementation/inventory binding differs')
        capture.capture(args.state,directory,check_existing=True)
    prebatch=recorded['pending_batch']['prebatch_state']
    expected_before={f'{index:04d}.{suffix}' for index in range(BEGIN)
                     for suffix in ['json','stdout','stderr']}
    if set(prebatch)!=expected_before:raise ValueError('original prefix inventory differs')
    current=capture.inventory(args.state)
    if set(current)!={f'{index:04d}.{suffix}' for index in range(END)
                      for suffix in ['json','stdout','stderr']}:
        raise ValueError('recovered receipt/log inventory is not the expected contiguous prefix')
    if any(current[name]!=digest for name,digest in prebatch.items()):
        raise ValueError('preexisting indexed evidence changed during interruption')

    repos,pins,_=external.setup(args.mathlib_root,args.lean_bin)
    plan_path=args.state/'PLAN.json'
    if (external.sha(plan_path)!='ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10'
            or plan_path.read_bytes()!=(HERE/'EXTERNAL-PLAN.json').read_bytes()):
        raise ValueError('selected external plan differs')
    plan=json.loads(plan_path.read_text())
    if (plan['compiler_sha256']!=external.LEAN_SHA or plan['mathlib_pin']!=external.PIN
            or plan['dependencies']!=pins or external.sha(plan_path)!=recorded['plan_sha256']
            or external.sha(args.mathlib_root/'lakefile.lean')!=external.MATHLIB_LAKEFILE_SHA):
        raise ValueError('compiler, dependency or Mathlib option source differs')
    events=[];summaries=[]
    for line in (batch/'stdout').read_text().splitlines():
        row=json.loads(line)
        if 'index' in row and 'module' in row:events.append(row)
        if row.get('status')=='BATCH_COMPLETE':summaries.append(row)
    expected_summary=dict(status='BATCH_COMPLETE',freshly_compiled=32,authenticated_reuse=BEGIN,
                          planned=len(plan['modules']),complete=False)
    if summaries!=[expected_summary] or [row['index'] for row in events]!=list(range(BEGIN,END)):
        raise ValueError('recovered batch event sequence/summary differs')
    if (batch/'stderr').read_bytes():raise ValueError('unexpected recovered outer stderr')
    ledger=[];recovered=[]
    for index,row in enumerate(plan['modules']):
        target=Path(row['target']);source=Path(row['source'])
        if index>=END:
            if external.artifacts(target):raise ValueError('unreceipted later planned objects exist')
            continue
        receipt_path=args.state/f'{index:04d}.json'
        receipt=json.loads(receipt_path.read_text())
        if receipt['exit_code']!=0 or any(receipt[key]!=value for key,value in row.items()):
            raise ValueError('recovered module selection differs: '+row['module'])
        if external.sha(source)!=row['source_sha256']:
            raise ValueError('selected source body changed: '+row['module'])
        actual=external.artifacts(target)
        if str(target) not in actual or not target.stat().st_size or actual!=receipt['artifacts']:
            raise ValueError('recovered module artifacts differ: '+row['module'])
        relative=Path(*row['module'].split('.')).with_suffix('.olean')
        found=[repo/'.lake/build/lib/lean'/relative for repo in repos
               if (repo/'.lake/build/lib/lean'/relative).is_file()]
        if not found or found[0]!=target:raise ValueError('selected import is shadowed')
        for suffix in ['stdout','stderr']:
            if external.sha(args.state/f'{index:04d}.{suffix}')!=receipt[suffix+'_sha256']:
                raise ValueError('recovered compiler output changed')
        ledger.append(dict(index=index,module=row['module'],receipt_sha256=external.sha(receipt_path),
                           source_sha256=row['source_sha256'],artifacts=actual))
        if index<BEGIN:continue
        expected_event=dict(module=row['module'],index=index,exit_code=0,seconds=receipt['seconds'])
        command=[str(args.lean_bin/'lean'),'-j','1','-s','8192','-R',row['repo'],
                 '-o',str(target),str(source)]
        if row['module'].startswith('Mathlib.'):command[1:1]=external.MATHLIB_OPTIONS
        if (events[index-BEGIN]!=expected_event or receipt['command']!=command
                or receipt.get('compiler_exit_code')!=0
                or receipt['runner_sha256']!=external.LOADED_SHA
                or receipt['frozen_helpers_sha256']!=external.pins['build_mathlib_serial.py']
                or receipt['resource_control']['helper_sha256']!=external.sha(HERE/'serial_compile.py')
                or receipt['execution']!='FRESH_SOURCE_COMPILE_ORIGINAL_ELABORATION'):
            raise ValueError('recovered compiler execution binding differs')
        for suffix in ['json','stdout','stderr']:
            copy(args.state/f'{index:04d}.{suffix}',args.out/'modules'/f'{index:04d}.{suffix}',
                 current[f'{index:04d}.{suffix}'])
        copy(source,args.out/'sources'/Path(*row['module'].split('.')).with_suffix('.lean'),row['source_sha256'])
        recovered.append(dict(index=index,receipt=receipt,receipt_sha256=ledger[-1]['receipt_sha256']))
    for source,digest in originals.items():
        if external.sha(Path(source))!=digest:raise ValueError('original recovery evidence changed during readback')
    end_processes=process_snapshot()
    save(args.out/'PREFIX-LEDGER.json',ledger)
    save(args.out/'RECOVERED-MODULE-RECEIPTS.json',recovered)
    result=dict(status='RECOVERED_MODULE_PREFIX_AUTHENTICATED',
        utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        runner_sha256=external.sha(Path(__file__)),plan_sha256=external.sha(plan_path),
        original_outer_guard_receipt_present=False,original_outer_guard_outcome='UNKNOWN',
        original_outer_guard_exit_code=None,original_outer_guard_elapsed_seconds=None,
        original_outer_guard_resource_maxima=None,original_interruption_cause='UNKNOWN',
        original_orchestrator_preserved_pending=True,original_files_sha256=originals,
        independently_pinned_recovery_snapshot=SNAPSHOT_PINS,
        recovery_snapshot_observed_utc='2026-10-13T23:14:00Z',
        completed059_stdout_first_observed_after_reconnection=True,
        freshly_compiled_in_recovery=0,reauthenticated_prefix=END,
        recovered_module_indices=list(range(BEGIN,END)),next_index=END,
        next_module=plan['modules'][END],recovered_batch_summary=expected_summary,
        sampled_module_resource_values_are_not_outer_guard_maxima=True,
        prefix_ledger_sha256=external.sha(args.out/'PREFIX-LEDGER.json'),
        recovered_module_ledger_sha256=external.sha(args.out/'RECOVERED-MODULE-RECEIPTS.json'),
        process_snapshots=dict(start=start_processes,end=end_processes),
        original_batch059_guard_success_claimed=False,original_batch042_outer_guard='UNKNOWN',original_batch057_outer_guard='UNKNOWN',
        prior_monitoring_file_supplied=False,
        adapter_compiled=False,
        resume_requires_new_readback_guard_success_and_explicit_coordinator_release=True)
    save(args.out/'RESULT.json',result)
    files=[dict(path=str(path.relative_to(args.out)),bytes=path.stat().st_size,
                sha256=external.sha(path)) for path in sorted(args.out.rglob('*')) if path.is_file()]
    save(args.out/'FILES.json',dict(files=files,binaries_included=False))
    print(json.dumps(dict(status=result['status'],prefix=END,next_index=END,
                         original_outer_guard_outcome='UNKNOWN',fresh_compilers=0,
                         result_sha256=external.sha(args.out/'RESULT.json'))),flush=True)


if __name__=='__main__':main()
