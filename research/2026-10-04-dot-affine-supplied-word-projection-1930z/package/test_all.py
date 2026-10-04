"""One reproducible fresh gate; all inherited providers remain byte-bound."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import sympy
import z3

ROOT=Path(__file__).resolve().parent

def bindings():
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(ROOT.rglob('*.py')) if 'prior-failure' not in p.parts
            and not any(part.startswith('checkpoint-') for part in p.relative_to(ROOT).parts)}

def main():
    for name in ['PROVIDER-BINDINGS.json','ACTUAL-SOURCE-PROVIDER-BINDINGS.json']:
        record=json.loads((ROOT/name).read_text())
        for row in record['files']:
            data=(ROOT/row['path']).read_bytes()
            assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
    before=bindings();attempts=[]
    for script,log in [('test_projection.py','FRESH-LINEAR-TEST.stdout'),
                       ('test_supplied_word.py','FRESH-WORD-TEST.stdout'),
                       ('execute_same_source.py','FRESH-ACTUAL-EXECUTION.stdout'),
                       ('test_carrier_preflight.py','FRESH-CARRIER-PREFLIGHT.stdout')]:
        started=time.monotonic()
        result=subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT,capture_output=True,text=True,
                              env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},timeout=120)
        (ROOT/log).write_text(result.stdout+result.stderr)
        attempts.append({'script':script,'exit_code':result.returncode,'seconds':time.monotonic()-started,
                         'stdout_file':log,'stdout_sha256':hashlib.sha256((ROOT/log).read_bytes()).hexdigest()})
        if result.returncode:
            (ROOT/'FRESH-AGGREGATE-RECEIPT.json').write_text(json.dumps({'status':'FAILED_FRESH_GATE','attempts':attempts},indent=2)+'\n')
            raise RuntimeError('Fresh test failed: '+script)
    assert before==bindings(),'Source changed during the fresh gate.'
    out={'status':'PASS_FRESH_SOURCE_SHARED_AFFINE_WORD_NUISANCE_RANK_AND_ACTUAL_EXECUTION_GATE',
         'software':{'python':sys.version.split()[0],'sympy':sympy.__version__,'z3':z3.get_version_string()},
         'source_bindings_before_after':before,'attempts':attempts,'source_bytes_stable':True,
         'old_lost_FM_evidence_inherited':False,'independent_review_status':'PENDING',
         'generic_action_search_nonlinear_QE_master_or_empirical_claimed':False}
    (ROOT/'FRESH-AGGREGATE-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'all_four_terminal_exits':0,
                      'software':out['software'],'independent_review':'PENDING'},indent=2))

if __name__=='__main__':main()
