#!/usr/bin/env python3
"""Replay the exact external plan with synchronous theorem elaboration.

Uses the frozen runner's source/toolchain authentication and artifact helpers.
The selected source bodies and imports are unchanged. Run under guard.py.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
PREVIOUS=HERE.parent/'2026-10-13-astra-unified-solver-0645z'
manifest=PREVIOUS/'PACKET-MANIFEST.json'
if hashlib.sha256(manifest.read_bytes()).hexdigest()!='728246e4960472a7319eb0b979660716d52ec82aa8799a2ef17f8bb23df77ef5':
    raise ValueError('published previous manifest changed')
pins={r['path']:r['sha256'] for r in json.loads(manifest.read_text())['files']}
if hashlib.sha256((PREVIOUS/'build_mathlib_serial.py').read_bytes()).hexdigest()!=pins['build_mathlib_serial.py']:
    raise ValueError('frozen compiler helpers changed')
sys.path.insert(0,str(PREVIOUS))
from build_mathlib_serial import setup,sha,artifacts,release_own_file_cache,LEAN_SHA,PIN

LOADED_SHA=sha(Path(__file__))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--mathlib-root',type=Path,required=True)
    p.add_argument('--lean-bin',type=Path,required=True)
    p.add_argument('--state',type=Path,required=True)
    p.add_argument('--batch',type=int,default=64)
    a=p.parse_args()
    if not 1<=a.batch<=64:raise ValueError('batch must contain at most64 fresh modules')
    a.mathlib_root=a.mathlib_root.resolve();a.lean_bin=a.lean_bin.resolve();a.state=a.state.resolve()
    if (a.state/'PLAN.json').read_bytes()!=(HERE/'EXTERNAL-PLAN.json').read_bytes():
        raise ValueError('external plan differs from selected complete closure')
    plan=json.loads((a.state/'PLAN.json').read_text())
    repos,dependencies,env=setup(a.mathlib_root,a.lean_bin)
    if plan['compiler_sha256']!=LEAN_SHA or plan['mathlib_pin']!=PIN or plan['dependencies']!=dependencies:
        raise ValueError('external compiler/dependency pin differs')
    fresh=reused=0
    for index,row in enumerate(plan['modules']):
        source=Path(row['source']);target=Path(row['target'])
        if sha(source)!=row['source_sha256']:raise ValueError('selected source changed')
        receipt=a.state/f'{index:04d}.json'
        if receipt.exists():
            old=json.loads(receipt.read_text())
            if old['exit_code'] or any(old[k]!=row[k] for k in row):
                raise ValueError('failed or altered receipt needs explicit repair: '+row['module'])
            actual=artifacts(target)
            if str(target) not in actual or old['artifacts']!=actual:
                raise ValueError('reused object identity differs: '+row['module'])
            for suffix in ['stdout','stderr']:
                if sha(a.state/f'{index:04d}.{suffix}')!=old[suffix+'_sha256']:
                    raise ValueError('reused compiler log differs')
            reused+=1;continue
        if fresh>=a.batch:break
        target.parent.mkdir(parents=True,exist_ok=True)
        command=[str(a.lean_bin/'lean'),'-DElab.async=false','-j','1','-s','8192',
                 '-R',row['repo'],'-o',str(target),str(source)]
        started=time.monotonic()
        stdout=a.state/f'{index:04d}.stdout';stderr=a.state/f'{index:04d}.stderr'
        with stdout.open('xb') as out,stderr.open('xb') as err:
            result=subprocess.run(command,cwd=row['repo'],env=env,stdout=out,stderr=err)
        actual=artifacts(target)
        code=result.returncode
        if not code and str(target) not in actual:code=2
        observed=dict(**row,command=command,exit_code=code,compiler_exit_code=result.returncode,
                      runner_sha256=LOADED_SHA,frozen_helpers_sha256=pins['build_mathlib_serial.py'],
                      execution='FRESH_SYNCHRONOUS_SOURCE_COMPILE',seconds=time.monotonic()-started,
                      artifacts=actual,stdout_sha256=sha(stdout),stderr_sha256=sha(stderr))
        receipt.write_text(json.dumps(observed,indent=2)+'\n')
        print(json.dumps(dict(module=row['module'],index=index,exit_code=code,seconds=observed['seconds'])),flush=True)
        if code:raise SystemExit(1)
        fresh+=1;release_own_file_cache(repos,a.lean_bin)
    print(json.dumps(dict(status='BATCH_COMPLETE',freshly_compiled=fresh,authenticated_reuse=reused,
                          planned=len(plan['modules']),complete=fresh+reused==len(plan['modules']))),flush=True)


if __name__=='__main__':main()
