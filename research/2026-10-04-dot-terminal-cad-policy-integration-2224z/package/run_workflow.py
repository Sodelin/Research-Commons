#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def hashes():
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in ROOT.rglob('*') if p.is_file() and (p.suffix in ('.py','.wl') or p.name in ('FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json','EXPORTED-ACTUAL-TERMINAL-SELECTOR.json'))}
before=hashes();results=[]
for script in ('assemble_cad_terminal_policy.py','execute_actual_cad_policy.py','test_cad_assembly_boundaries.py'):
    result=subprocess.run([sys.executable,script],cwd=ROOT,capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
    (ROOT/(script.replace('.py','')+'.stdout')).write_text(result.stdout+result.stderr)
    results.append({'script':script,'exit_code':result.returncode,'stdout_sha256':hashlib.sha256((result.stdout+result.stderr).encode()).hexdigest()})
    print(result.stdout,end='');print(result.stderr,end='',file=sys.stderr)
    if result.returncode:break
status='PASS_SOURCE_DERIVED_TERMINAL_CAD_POLICY_WORKFLOW' if len(results)==3 and all(r['exit_code']==0 for r in results) and before==hashes() else 'FAILED_OR_INCOMPLETE_WORKFLOW'
receipt={'status':status,'processes':results,'source_and_provider_hashes_before':before,'source_and_provider_hashes_after':hashes(),'source_unchanged_during_workflow':before==hashes(),'python_version':sys.version,'Wolfram_execution':'stored complete backend receipt, not rerun by this command'}
(ROOT/'WORKFLOW-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':status,'terminal_exit_codes':[r['exit_code'] for r in results]}));sys.exit(0 if status.startswith('PASS_') else 1)
