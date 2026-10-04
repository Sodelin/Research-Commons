"""One connected source-admitted synthesis, coverage and execution gate."""
import hashlib,json,os,subprocess,sys,time
from pathlib import Path
import sympy,z3

ROOT=Path(__file__).resolve().parent

def hashes():
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(ROOT.rglob('*.py'))
            if not any(x.startswith('checkpoint-') for x in p.relative_to(ROOT).parts)}

def main():
    start=hashes();attempts=[]
    for script,log in [('synthesize_policy.py','SYNTHESIS.stdout'),
                       ('execute_generated_policy.py','ACTUAL-EXECUTION.stdout'),
                       ('test_policy_synthesis.py','CONTROLS.stdout'),
                       ('test_endpoint_branch.py','ENDPOINT-BRANCH.stdout')]:
        before=time.monotonic()
        r=subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT,capture_output=True,text=True,
                         env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},timeout=120)
        (ROOT/log).write_text(r.stdout+r.stderr)
        attempts.append({'script':script,'exit_code':r.returncode,'seconds':time.monotonic()-before,
                         'stdout':log,'stdout_sha256':hashlib.sha256((ROOT/log).read_bytes()).hexdigest()})
        if r.returncode:raise RuntimeError('Workflow step failed: '+script)
    assert start==hashes(),'Source changed during the workflow.'
    result={'status':'PASS_CONNECTED_AUTOMATIC_ADAPTIVE_POLICY_SYNTHESIS_SOURCE_COVERAGE_AND_EXECUTION',
            'attempts':attempts,'source_bindings_before_after':start,'software':{'python':sys.version.split()[0],'sympy':sympy.__version__,'z3':z3.get_version_string()},
            'independent_review_status':'PENDING','supported_provider':'Previously accepted complete n4/r1 two-original-forcing image',
            'word_supplied_by_caller':False,'finite_section_constructor_general_G7_complete':False,
            'earlier_one_call_optimum_preserved':True,'new_source_census_Lean_G3_G4_empirical_claimed':False}
    (ROOT/'WORKFLOW-RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'all_four_terminal_exits':0,
                      'automatic_complete_policy_instance':True,'general_G7_complete':False},indent=2))

if __name__=='__main__':main()
