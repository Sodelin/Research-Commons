#!/usr/bin/env python3
"""Authored bounded launcher provenance and semantic CLI regressions; fresh output required."""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import time
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[3]
APP = ROOT / 'applications/practical-solver'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def limits():
    resource.setrlimit(resource.RLIMIT_CPU, (80, 80))
    resource.setrlimit(resource.RLIMIT_AS, (768 * 2**20, 768 * 2**20))
    resource.setrlimit(resource.RLIMIT_FSIZE, (32 * 2**20, 32 * 2**20))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

def injected(args):
    spec = importlib.util.spec_from_file_location('_release_fault_injection', APP / 'run.py')
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    if args.fault == 'component-exit':
        original_execute=module.execute
        def execute(out,name,command,**kwargs):
            return original_execute(out,name,[sys.executable,'-B','-c','raise SystemExit(1)'],**kwargs)
        module.execute=execute
        return module.component(SimpleNamespace(command='forest-baseline',output=args.output,
            request=ROOT/'research/2026-10-09-codex-conditional-bridge-1630z/graph/examples/one-ordinary-population.json'))
    if args.fault == 'staging':
        def stage(_):
            raise OSError('INJECTED isolated staging failure')
        module.stage = stage
    elif args.fault == 'authentication':
        original_stage = module.stage
        def stage(out):
            runtime, engine = original_stage(out)
            path = engine / 'global_engine.py'; path.chmod(0o644)
            path.write_bytes(path.read_bytes() + b'\n# INJECTED isolated staged-source corruption\n')
            return runtime, engine
        module.stage = stage
    elif args.fault == 'launch':
        def popen(*_, **__):
            raise OSError('INJECTED Popen refusal before process creation')
        module.subprocess.Popen = popen
    elif args.fault in ('producer-exit', 'checker-exit'):
        original_execute = module.execute
        victim = args.fault.split('-')[0]
        def execute(out, name, command, **kwargs):
            if name == victim:
                command = [sys.executable, '-B', '-c', 'raise SystemExit(19)']
            return original_execute(out, name, command, **kwargs)
        module.execute = execute
    return module.run(SimpleNamespace(example='informative', request=None, output=args.output, native_binary=None))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--backend-python',type=Path,help='Optional already-provisioned pinned scratch backend')
    parser.add_argument('--fault', choices=['staging', 'authentication', 'launch', 'producer-exit', 'checker-exit','component-exit'])
    args = parser.parse_args()
    if args.fault:
        return injected(args)
    out = args.output.absolute(); out.mkdir(parents=True, exist_ok=False)
    (out / 'logs').mkdir(); cases = []
    paths = [APP/'run.py', APP/'README.md', APP/'SOURCE-IDENTITIES.json', APP/'certified_bounds.py', APP/'forest_baseline.py',
             APP.parent/'practical-solver-biology/ingestion.py']
    before = {str(p.relative_to(ROOT)):digest(p) for p in paths}
    env = {'PATH':os.defpath, 'LANG':'C.UTF-8', 'PYTHONNOUSERSITE':'1', 'PYTHONDONTWRITEBYTECODE':'1', 'PYTHONHASHSEED':'0'}
    cli = [sys.executable, '-B', str(APP/'run.py')]
    def record(name, command, expected=0, assertion=None):
        started = time.monotonic()
        row = {'name':name, 'command':command, 'expected_exit_code':expected}
        try:
            p = subprocess.run(command, cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               timeout=110, preexec_fn=limits)
            (out/'logs'/(name+'.stdout')).write_bytes(p.stdout)
            (out/'logs'/(name+'.stderr')).write_bytes(p.stderr)
            row.update(exit_code=p.returncode, wall_seconds=time.monotonic()-started,
                       stdout_sha256=hashlib.sha256(p.stdout).hexdigest(), stderr_sha256=hashlib.sha256(p.stderr).hexdigest())
            assert p.returncode == expected, p.stderr[:500]
            if assertion:
                assertion(row, p)
            row['passed'] = True
        except Exception as error:
            row.update(passed=False, error_type=type(error).__name__, error=str(error))
        cases.append(row)
        (out/'RESULTS.json').write_text(json.dumps({'status':'IN_PROGRESS','cases':cases,'source_before':before}, indent=2)+'\n')
        print(json.dumps({k:row[k] for k in ('name','passed','error') if k in row}), flush=True)
    def result_at(directory, row):
        r=json.loads((directory/'RESULT.json').read_bytes())
        row.update(output=str(directory),status=r['status'],solver_called=r.get('solver_called'),
                   checker_called=r.get('checker_called'),diagnostic_called=r.get('diagnostic_called'))
        for flag in ('source_feasibility_certified','statistical_coverage_verified','parameter_accuracy_released'):
            assert r[flag] is False
        assert all((directory/n).is_file() for n in ('RESULT.json','REPORT.md','REPORT.html','ARTIFACTS.json'))
        return r
    def fault_assertion(name, launched, checked=False):
        def verify(row, _):
            directory=out/name; r=result_at(directory,row)
            assert r['status']=='RESOURCE_OR_EXECUTION_FAILURE'
            assert r['solver_called'] is launched and r['checker_called'] is checked and r['diagnostic_called'] is False
            assert (directory/'producer.execution.json').exists() == (launched or name=='launch')
            assert not (directory/'checker.stdout').exists() if not checked else (directory/'checker.execution.json').is_file()
            if name in ('staging','authentication','manifest-tamper'):
                assert not (directory/'producer.stdout').exists()
            if name=='launch':
                assert json.loads((directory/'producer.execution.json').read_bytes())['process_started'] is False
            if launched:
                receipt=json.loads((directory/(('checker' if checked else 'producer')+'.execution.json')).read_bytes())
                assert receipt['process_started'] is True and receipt['exit_code']==19
        return verify
    # A literal manifest tamper in a disposable app copy; published bytes unchanged.
    sandbox=out/'isolated'; (sandbox/'applications').mkdir(parents=True)
    copied=sandbox/'applications/practical-solver'; shutil.copytree(APP,copied)
    (sandbox/'research').symlink_to(ROOT/'research',target_is_directory=True)
    manifest=json.loads((copied/'SOURCE-IDENTITIES.json').read_bytes());manifest['engine_directory']='tampered-before-dispatch'
    (copied/'SOURCE-IDENTITIES.json').write_text(json.dumps(manifest)+'\n')
    record('manifest-tamper',[sys.executable,'-B',str(copied/'run.py'),'run','--example','informative','--output',str(out/'manifest-tamper')],1,fault_assertion('manifest-tamper',False))
    for fault in ('staging','authentication','launch','producer-exit','checker-exit'):
        record(fault,[sys.executable,'-B',str(Path(__file__).resolve()),'--fault',fault,'--output',str(out/fault)],1,
               fault_assertion(fault,fault in ('producer-exit','checker-exit'),fault=='checker-exit'))
    def semantic(name):
        def verify(row,_):
            directory=out/name; r=result_at(directory,row)
            if name in ('informative','finite-data'):
                checked=r['original_complete_checker']; request=json.loads((directory/'REQUEST.json').read_bytes())
                assert r['solver_called'] is True and r['checker_called'] is True
                assert checked['details']['complete_numeric_replay'] and r['retained_complete_outer_cover']==checked['physical_cover']
                for parameter,width in r['widths'].items():
                    lower=min(Fraction(c['box'][parameter][0]) for c in checked['physical_cover'])
                    upper=max(Fraction(c['box'][parameter][1]) for c in checked['physical_cover'])
                    ratio=(upper-lower)/(Fraction(request['box'][parameter][1])-Fraction(request['box'][parameter][0]))
                    assert ratio == Fraction(width['normalized_ratio'])
                if name=='informative':
                    assert r['status']=='CONDITIONAL_UNION_WIDTH_CERTIFIED'
                    assert max(Fraction(w['normalized_ratio']) for w in r['widths'].values())==Fraction(17394377843899475,4611686018427387904)
                else:
                    assert r['status']=='UNKNOWN_OUTER_COVER' and all(Fraction(w['normalized_ratio'])==1 for w in r['widths'].values())
                    assert len(checked['physical_cover'])==2 and '3/55' in r['explanation']
                    assert r['saved_finite_data_obstruction']['execution_mode']=='SAVED_AUTHENTICATED_EVIDENCE'
                assert r['native_reference_post_checker']['native_called'] is False
            elif name=='unsupported':
                assert r['status']=='MODEL_NOT_ADMITTED' and r['solver_called'] is False and not (directory/'producer.stdout').exists()
            elif name=='saved':
                assert r['execution_mode']=='SAVED_RESULTS' and r['solver_called'] is False and r['checker_called'] is False
                assert 'Saved results' in (directory/'REPORT.html').read_text()
            elif name=='recheck':
                assert r['execution_mode']=='FRESH_INDEPENDENT_RECHECK' and r['solver_called'] is False and r['checker_called'] is True
                assert r['status']=='CONDITIONAL_UNION_WIDTH_CERTIFIED' and r['original_complete_checker']['details']['complete_numeric_replay']
        return verify
    for name in ('informative','finite-data','unsupported'):
        record(name,cli+['run','--example',name,'--output',str(out/name)],assertion=semantic(name))
    record('saved',cli+['show','--example','informative','--output',str(out/'saved')],assertion=semantic('saved'))
    record('recheck',cli+['check','--run',str(out/'informative'),'--output',str(out/'recheck')],assertion=semantic('recheck'))
    def molecular(row,_):
        r=json.loads((out/'molecular/RESULT.json').read_bytes())
        assert r['evidence']=='MOCK_SYNTHETIC' and r['execution_mode']=='FRESH_OFFLINE_FIXTURE_COMPUTATION'
        assert r['live_api_calls']==0 and r['credentials_accessed'] is False and r['ancestry_observation_admitted'] is False
        assert all(x['evidence']=='MOCK_SYNTHETIC' for x in r['interactions'].values())
        row.update(status=r['status'],evidence=r['evidence'],live_api_calls=r['live_api_calls'])
    record('molecular',cli+['molecular','--output',str(out/'molecular')],assertion=molecular)
    def audit(row,p):
        r=json.loads(p.stdout)
        assert r['audit_kind']=='ARCHIVED_PANEL_AUDIT' and r['loci']==1024 and r['mean_conversion_count']==1
        assert r['normalized_rA_separation']=='3/55' and r['scientific_confidence_admitted'] is False and r['fresh_data'] is False
        row.update(status=r['status'],audit_kind=r['audit_kind'],loci=r['loci'])
    record('archived-panel-audit',[sys.executable,'-B',str(APP.parent/'practical-solver-biology/ingestion.py')],assertion=audit)
    def component_assertion(name):
        def verify(row,_):
            directory=out/name;r=json.loads((directory/'RESULT.json').read_bytes())
            assert r['execution_mode']=='FRESH_COMPONENT_EXECUTION' and r['component_called'] is True
            assert r['original_nine_parameter_producer_called'] is False and r['component_source_unchanged'] is True
            assert r['statistical_coverage_verified'] is False and r['whole_application_lean_verified'] is False
            assert all((directory/n).is_file() for n in ('REPORT.md','REPORT.html','ARTIFACTS.json'))
            row.update(status=r['status'],component_called=r['component_called'])
            if name=='conditional-count':
                c=r['component_result'];count=c['conditional_counts'][0]
                assert r['status']=='UNKNOWN' and c['reason']=='UNKNOWN_PROVIDER_VERIFIER_UNAVAILABLE'
                assert count['delta']=='1/2' and count['rational_upper_bound']=='24' and count['cell_count_bound']==24
                assert count['ceiling_check'] and c['provider_verified'] is False and c['bound_applied_to_catalogue'] is False
                assert c['solver_called'] is False and c['checker_called'] is False
            elif name=='backend-unavailable':
                c=r['component_result']
                assert r['status']=='UNKNOWN' and c['reason']=='UNKNOWN_BACKEND_UNAVAILABLE'
                assert c['solver_called'] is False and c['checker_called'] is False and c['unrestricted_NO_claimed'] is False
            elif name=='forest-baseline':
                c=r['component_result'];p=c['probability']
                assert r['status']=='EXACT_CLASSICAL_COORDINATE' and Fraction(int(p['numerator_hex'],16),int(p['denominator_hex'],16))==Fraction(7,192)
                assert c['histories']==1 and c['source_witness'] is False and c['quantum_advantage_established'] is False
                assert c['evolution']=='ordinary_stochastic_exp_tQ'
            else:
                assert r['status']=='REFUSED_REQUEST' and 'component_result' not in r
        return verify
    record('conditional-count',cli+['certified-bounds','--request',str(APP/'examples/certified-bounds/conditional-count-unknown.json'),'--output',str(out/'conditional-count')],2,component_assertion('conditional-count'))
    record('backend-unavailable',cli+['certified-bounds','--request',str(APP/'examples/certified-bounds/finite-witness.json'),'--python-executable',str(out/'NO-BACKEND-PYTHON'),'--output',str(out/'backend-unavailable')],2,component_assertion('backend-unavailable'))
    forest=ROOT/'research/2026-10-09-codex-conditional-bridge-1630z/graph/examples/one-ordinary-population.json'
    record('forest-baseline',cli+['forest-baseline','--request',str(forest),'--output',str(out/'forest-baseline')],assertion=component_assertion('forest-baseline'))
    invalid=json.loads(forest.read_bytes());invalid['survival']['numerator']=0
    invalid_path=out/'zero-survival.json';invalid_path.write_text(json.dumps(invalid)+'\n')
    record('forest-refusal',cli+['forest-baseline','--request',str(invalid_path),'--output',str(out/'forest-refusal')],2,component_assertion('forest-refusal'))
    def component_crash(row,_):
        directory=out/'component-crash';r=json.loads((directory/'RESULT.json').read_bytes())
        receipt=json.loads((directory/'forest-baseline.execution.json').read_bytes())
        assert r['status']=='RESOURCE_OR_EXECUTION_FAILURE' and r['component_called'] is True
        assert receipt['process_started'] is True and receipt['exit_code']==1
        assert not (directory/'component/RESULT.json').exists() and 'component_result' not in r
        row.update(status=r['status'],component_called=True)
    record('component-crash',[sys.executable,'-B',str(Path(__file__).resolve()),'--fault','component-exit','--output',str(out/'component-crash')],1,component_crash)
    if args.backend_python:
        for example,status,exit_code in [('finite-witness','CERTIFIED_SOURCE_WITNESS',0),
                                         ('shared-row-exclusion','CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS',0),
                                         ('bounded-exhaustion','UNKNOWN',2)]:
            name='backend-'+example
            def backend_assertion(row,_,name=name,status=status):
                directory=out/name;r=json.loads((directory/'RESULT.json').read_bytes());c=r['component_result']
                assert r['status']==c['status']==status and c['solver_called'] is True
                assert c['unrestricted_NO_claimed'] is False and c['general_G3_resolved'] is False
                if status.startswith('CERTIFIED_'):
                    assert c['checker_called'] is True and c['checker_execution']['returncode']==0
                    assert 'semantic_check' in c
                    assert c['source_feasibility_certified'] is (status=='CERTIFIED_SOURCE_WITNESS')
                row.update(status=status,solver_called=c['solver_called'],checker_called=c['checker_called'])
            record(name,cli+['certified-bounds','--request',str(APP/('examples/certified-bounds/'+example+'.json')),
                            '--python-executable',str(args.backend_python.absolute()),'--output',str(out/name)],exit_code,backend_assertion)
    after={str(p.relative_to(ROOT)):digest(p) for p in paths}
    result={'schema':'release-regression-v1','status':'PASS' if all(r['passed'] for r in cases) and before==after else 'FAILED',
            'passed':sum(r['passed'] for r in cases),'total':len(cases),'cases':cases,'source_before':before,'source_after':after,
            'production_sources_unchanged':before==after,'python':sys.version,'resource_caps':{'cpu_seconds':80,'wall_seconds':110,'address_space_bytes':768*2**20,'per_file_bytes':32*2**20},
            'evidence_tier':'AUTHORED_EXECUTION; independent validation separate; no whole-application proof'}
    (out/'RESULTS.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':result['status'],'passed':result['passed'],'total':result['total']}),flush=True)
    return 0 if result['status']=='PASS' else 1

if __name__=='__main__':
    raise SystemExit(main())
