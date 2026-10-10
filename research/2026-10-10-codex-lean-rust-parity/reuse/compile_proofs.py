#!/usr/bin/env python3
"""Compile each exact owned source, retaining failed attempts and prior bytes.

Invoke under `/workspace/toolchains/lean-4.33.1-linux/bin/lake env` from the
pinned mathlib checkout. No previous mathematical proof objects are required.
"""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
LEAN = Path('/workspace/toolchains/lean-4.33.1-linux/bin/lean')
env = dict(os.environ)
env['LEAN_PATH'] = ':'.join([str(HERE/'build'), str(BASE/'lean/.lake/build/lib/lean'), env.get('LEAN_PATH','')])
for target in sys.argv[1:]:
    src = (HERE/'derived-providers' if target == 'StrictAffineElimination' else HERE/'sources') / (target+'.lean')
    content = src.read_bytes()
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    evidence = HERE/'evidence'/f'{stamp}-{target}'
    evidence.mkdir(parents=True)
    (evidence/'source.lean').write_bytes(content)
    flags = ['-j1','-t0','-M4096','--trust=0','-Ddebug.skipKernelTC=false']
    command = [str(LEAN), *flags, '-R',str(src.parent),str(src),'-o',str(HERE/'build'/(target+'.olean'))]
    proc = subprocess.run(command,env=env,capture_output=True,text=True)
    (evidence/'stdout.txt').write_text(proc.stdout)
    (evidence/'stderr.txt').write_text(proc.stderr)
    receipt={'module':target,'source_path':str(src),'source_sha256':hashlib.sha256(content).hexdigest(),
        'command':command,'LEAN_PATH':env['LEAN_PATH'],'exit_code':proc.returncode,
        'status':'PASS_NEW_KERNEL_CHECK' if proc.returncode==0 else 'FAIL_PRESERVED',
        'started_utc':stamp,'evidence_path':str(evidence)}
    obj=HERE/'build'/(target+'.olean')
    if proc.returncode==0: receipt['olean_sha256']=hashlib.sha256(obj.read_bytes()).hexdigest()
    (evidence/'RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    print(proc.stdout,flush=True)
    print(proc.stderr,flush=True)
    if proc.returncode: sys.exit(proc.returncode)
