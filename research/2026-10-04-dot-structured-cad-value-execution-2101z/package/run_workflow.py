#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def hashes():
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in ROOT.rglob('*') if p.is_file() and (p.suffix in ('.py','.wl') or p.name in ('THREE-CALL-POLICY.json','FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json','EXPORTED-CAD-VALUES.json'))}
before=hashes();results=[]
for script in ('test_cad_values.py','execute_source_cad_values.py'):
    result=subprocess.run([sys.executable,script],cwd=ROOT,capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    (ROOT/(script.replace('.py','')+'.stdout')).write_text(result.stdout+result.stderr)
    results.append({'script':script,'exit_code':result.returncode,'stdout_sha256':hashlib.sha256((result.stdout+result.stderr).encode()).hexdigest()})
    print(result.stdout,end='');print(result.stderr,end='',file=sys.stderr)
    if result.returncode:break
status='PASS_STRUCTURED_CAD_VALUE_WORKFLOW' if len(results)==2 and all(r['exit_code']==0 for r in results) and before==hashes() else 'FAILED_OR_INCOMPLETE_WORKFLOW'
receipt={'status':status,'processes':results,'source_and_provider_hashes_before':before,'source_and_provider_hashes_after':hashes(),'source_unchanged_during_workflow':before==hashes(),'python_version':sys.version}
(ROOT/'WORKFLOW-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':status,'terminal_exit_codes':[r['exit_code'] for r in results]}))
sys.exit(0 if status=='PASS_STRUCTURED_CAD_VALUE_WORKFLOW' else 1)
