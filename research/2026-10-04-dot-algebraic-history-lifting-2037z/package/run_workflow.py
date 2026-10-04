#!/usr/bin/env python3
"""Terminal aggregate over only this newly authored execution gate."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parent
def hashes():
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in ROOT.rglob('*') if p.is_file() and (p.suffix=='.py' or p.name=='FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json')}
before=hashes();results=[]
for script in ('test_history_points.py','test_three_call_policy.py','execute_three_call_source.py'):
    result=subprocess.run([sys.executable,script],cwd=ROOT,capture_output=True,text=True,
                          env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    (ROOT/(script.replace('.py','')+'.stdout')).write_text(result.stdout+result.stderr)
    results.append({'script':script,'exit_code':result.returncode,'stdout_sha256':hashlib.sha256((result.stdout+result.stderr).encode()).hexdigest()})
    print(result.stdout,end='');print(result.stderr,end='',file=sys.stderr)
    if result.returncode:break
receipt={'status':'PASS_ALGEBRAIC_HISTORY_LIFT_WORKFLOW' if len(results)==3 and all(r['exit_code']==0 for r in results) and before==hashes() else 'FAILED_OR_INCOMPLETE_WORKFLOW',
         'processes':results,'source_and_provider_hashes_before':before,'source_and_provider_hashes_after':hashes(),
         'python_version':sys.version,'source_unchanged_during_workflow':before==hashes()}
(ROOT/'WORKFLOW-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':receipt['status'],'terminal_exit_codes':[r['exit_code'] for r in results]}))
sys.exit(0 if receipt['status']=='PASS_ALGEBRAIC_HISTORY_LIFT_WORKFLOW' else 1)
