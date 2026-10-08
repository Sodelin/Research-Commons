#!/usr/bin/env python3
"""Bounded Linux full-CLI benchmark; never installs/builds; no kernel-only claim."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parents[1]

def measure(command):
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        started=time.perf_counter()
        child=subprocess.Popen(command,cwd=ROOT,stdout=stdout,stderr=stderr)
        _,status,usage=os.wait4(child.pid,0)
        elapsed=time.perf_counter()-started
        child.returncode=os.waitstatus_to_exitcode(status)
        stdout.seek(0); output=stdout.read()
        stderr.seek(0); errors=stderr.read()
        assert child.returncode==0 and not errors,(command,child.returncode,errors)
        return output,{'wall_seconds':elapsed,'user_cpu_seconds':usage.ru_utime,
                       'system_cpu_seconds':usage.ru_stime,'peak_rss_kib':usage.ru_maxrss,
                       'output_bytes':len(output)}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',type=Path,default=ROOT/'target/release/count-certificate')
    parser.add_argument('--repetitions',type=int,default=7)
    args=parser.parse_args()
    assert platform.system()=='Linux','RSS units and wait4 contract are Linux-specific'
    assert 3<=args.repetitions<=20,'bounded range: 3..20 repetitions'
    binary=args.binary.resolve()
    assert binary.is_file(),'build the candidate first'
    check=json.loads((ROOT/'evidence/check-report.json').read_text())
    digest=hashlib.sha256(binary.read_bytes()).hexdigest()
    assert check['differential']=='PASS' and check['binary_sha256']==digest,'candidate must have passing differential evidence'
    workloads=[['0','1/2'],['1','1e-12'],['10','1e-15'],['25','1e-8','--weights'],
               ['100','1/2','--max-steps','2']]
    results=[]
    for cli in workloads:
        rows={'python':[],'rust':[]}; outputs={}
        for i in range(args.repetitions):
            # Alternate order to reduce simple ordering bias; no cache clearing.
            for engine in (['python','rust'] if i%2==0 else ['rust','python']):
                cmd=([sys.executable,str(ROOT/'reference/count_certificate.py')] if engine=='python' else [str(binary)])+cli
                output,measurement=measure(cmd)
                rows[engine].append(measurement); outputs[engine]=output
            assert outputs['python']==outputs['rust'],'byte-exact result changed'
        summary={engine:{metric:{'median':statistics.median([r[metric] for r in samples]),
                                  'min':min(r[metric] for r in samples),
                                  'max':max(r[metric] for r in samples)}
                         for metric in samples[0]} for engine,samples in rows.items()}
        result=json.loads(outputs['rust'])
        results.append({'argv':cli,'status':result['status'],'inspected':result['inspected'],
                        'samples':rows,'summary':summary})
    report={'status':'MEASURED_FULL_CLI_ONLY','finished_utc':datetime.now(timezone.utc).isoformat(),
            'platform':platform.platform(),'python':sys.version,'binary_sha256':digest,
            'repetitions':args.repetitions,'binary_bytes':binary.stat().st_size,
            'limitations':['Small bounded synthetic corpus; not a solver-wide performance claim.',
                            'Includes startup, argument parsing, arithmetic, serialization and OS scheduling.',
                            'No controlled cold-cache experiment; no kernel-only measurement.',
                            'RSS is Linux wait4 ru_maxrss (KiB); subprocess-launch floors may dominate. Uniform RSS is not evidence of memory equivalence.',
                            'Wall-clock measurements are descriptive, not formal guarantees.'],
            'workloads':results}
    (ROOT/'evidence/benchmark-report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    for r in results:
        print(' '.join(r['argv']),json.dumps({k:v['wall_seconds'] for k,v in r['summary'].items()}))
    return 0

if __name__=='__main__': raise SystemExit(main())
