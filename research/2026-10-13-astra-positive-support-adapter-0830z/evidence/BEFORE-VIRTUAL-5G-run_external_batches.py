#!/usr/bin/env python3
"""Run a bounded number of serial guarded batches; stop on any failure/pause."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from capture_batch import capture,inventory,LOADED_SHA as CAPTURE_SHA

HERE=Path(__file__).resolve().parent
PREVIOUS=HERE.parent/'2026-10-13-astra-unified-solver-0645z'
ROOT=HERE.parent.parent

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--first-batch',type=int,required=True)
p.add_argument('--batches',type=int,default=3)
p.add_argument('--batch-size',type=int,default=64)
p.add_argument('--state',type=Path,required=True)
p.add_argument('--mathlib-root',type=Path,required=True)
p.add_argument('--lean-bin',type=Path,required=True)
a=p.parse_args()
if not 1<=a.batches<=3 or not 1<=a.batch_size<=64:
    raise ValueError('at most three 64-module batches per invocation')
if (a.state/'PLAN.json').read_bytes()!=(HERE/'EXTERNAL-PLAN.json').read_bytes():
    raise ValueError('external selection differs from published checkpoint')
manifest_path=PREVIOUS/'PACKET-MANIFEST.json'
if digest(manifest_path)!='728246e4960472a7319eb0b979660716d52ec82aa8799a2ef17f8bb23df77ef5':
    raise ValueError('published previous packet manifest differs')
manifest=json.loads(manifest_path.read_text())
pins={r['path']:r['sha256'] for r in manifest['files']}
for name in ['guard.py','build_mathlib_serial.py']:
    if digest(PREVIOUS/name)!=pins[name]:raise ValueError('frozen runner changed')
record=dict(runner_sha256=digest(Path(__file__)),capture_runner_sha256=CAPTURE_SHA,first_batch=a.first_batch,
            requested_batches=a.batches,batch_size=a.batch_size,
            plan_sha256=digest(HERE/'EXTERNAL-PLAN.json'),batches=[])
recordpath=HERE/'evidence'/f'ORCHESTRATOR-{a.first_batch:03d}.json'
with recordpath.open('x') as f:json.dump(record,f,indent=2);f.write('\n')
for number in range(a.first_batch,a.first_batch+a.batches):
    if (HERE/'PAUSE-BUILDS').exists():
        print(json.dumps(dict(status='PAUSED_BEFORE_NEXT_BATCH',next_batch=number)),flush=True)
        break
    output=HERE/'evidence'/f'external-batch-{number:03d}'
    before=inventory(a.state)
    record['pending_batch']=dict(number=number,prebatch_state=before)
    recordpath.write_text(json.dumps(record,indent=2)+'\n')
    command=[sys.executable,str(PREVIOUS/'guard.py'),'--out',str(output),'--cwd',str(ROOT),
             '--wall','900','--cpu','600','--memory-mib','4096','--file-mib','1024','--',
             sys.executable,'-B',str(HERE/'build_external_serial.py'),
             '--mathlib-root',str(a.mathlib_root),'--lean-bin',str(a.lean_bin),
             '--state',str(a.state),'--batch',str(a.batch_size)]
    result=subprocess.run(command,cwd=ROOT)
    with (output/'PRE-BATCH-STATE.json').open('x') as f:json.dump(before,f,indent=2);f.write('\n')
    del record['pending_batch']
    record['batches'].append(dict(number=number,command=command,exit_code=result.returncode,
                                  receipt_sha256=digest(output/'RECEIPT.json')))
    recordpath.write_text(json.dumps(record,indent=2)+'\n')
    capture(a.state,output)
    if result.returncode:
        print(json.dumps(dict(status='STOPPED_ON_FAILED_BATCH',batch=number)),flush=True)
        raise SystemExit(result.returncode)
    last=json.loads((output/'stdout').read_text().splitlines()[-1])
    print(json.dumps(dict(last,batch=number,orchestration_status='BATCH_CHECKPOINT')),flush=True)
    if last.get('complete'):break
