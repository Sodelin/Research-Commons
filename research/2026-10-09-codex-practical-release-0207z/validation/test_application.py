"""Independent bounded CLI regressions. Creates a new evidence directory."""
import argparse
import copy
from fractions import Fraction as Q
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
APP = ROOT / 'applications/practical-solver'
CLI = [sys.executable, '-B', str(APP / 'run.py')]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--native-binary', type=Path)
    a = parser.parse_args()
    out = a.output.absolute(); out.mkdir(parents=True, exist_ok=False)
    (out / 'cases').mkdir(); (out / 'requests').mkdir()
    results = []
    reviewed_paths = sorted([APP/'run.py', APP/'diagnostic.py', APP/'SOURCE-IDENTITIES.json', *APP.glob('examples/*.json'),
                             *APP.parent.glob('practical-solver-biology/*.py')])
    source_before = {str(p.relative_to(ROOT)): digest(p) for p in reviewed_paths}

    def record(name, args, code=0, status=None, check=None):
        started = time.monotonic()
        command = CLI + args
        def limits():
            resource.setrlimit(resource.RLIMIT_CPU, (80,80))
            resource.setrlimit(resource.RLIMIT_AS, (768*2**20,768*2**20))
            resource.setrlimit(resource.RLIMIT_FSIZE, (32*2**20,32*2**20))
            resource.setrlimit(resource.RLIMIT_CORE,(0,0))
        env = dict(PATH=os.defpath, LANG='C.UTF-8', PYTHONNOUSERSITE='1', PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0',
                   ALPHAGENOME_API_KEY='SENTINEL-NO-LIVE-KEY', GH_TOKEN='SENTINEL-NO-GH-KEY')
        try:
            p = subprocess.run(command,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=110,preexec_fn=limits)
            row = dict(name=name,command=command,exit_code=p.returncode,wall_seconds=time.monotonic()-started,
                       expected_exit_code=code,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stderr_sha256=hashlib.sha256(p.stderr).hexdigest())
            (out / 'cases' / (name+'.stdout')).write_bytes(p.stdout)
            (out / 'cases' / (name+'.stderr')).write_bytes(p.stderr)
            assert p.returncode == code, f'Exit {p.returncode}, expected {code}: {p.stderr[:600]!r}'
            if code == 0:
                summary = json.loads(p.stdout)
                directory = Path(summary['output'])
                result = json.loads((directory / 'RESULT.json').read_bytes())
                row.update(output=str(directory),status=result['status'])
                if status: assert result['status'] == status
                if result.get('schema')=='practical-solver-offline-molecular-v1':
                    assert result['live_api_calls']==0 and result['credentials_accessed'] is False and result['ancestry_observation_admitted'] is False
                else:
                    for flag in ('source_feasibility_certified','statistical_coverage_verified','parameter_accuracy_released'):
                        assert result[flag] is False
                assert all((directory / x).is_file() for x in ('REPORT.md','REPORT.html','RESULT.json','ARTIFACTS.json'))
                if check: check(result,directory)
            row['passed'] = True
        except Exception as error:
            row = locals().get('row',dict(name=name,command=command,wall_seconds=time.monotonic()-started))
            row.update(passed=False,error_type=type(error).__name__,error=str(error))
        results.append(row)
        (out / 'RESULTS.json').write_text(json.dumps(dict(status='IN_PROGRESS',cases=results,source_before=source_before),indent=2)+'\n')
        print(json.dumps({k:row[k] for k in ('name','passed','status','error') if k in row}),flush=True)
        return row

    def newpath(name): return out / name
    def fresh(name,extra=None,status=None,check=None):
        return record(name,['run','--example',name,'--output',str(newpath(name))]+(extra or []),status=status,check=check)
    def widths_exact(result,directory):
        checked=result['original_complete_checker']
        request=json.loads((directory/'REQUEST.json').read_bytes())
        for k,row in checked['widths'].items():
            lo=min(Q(c['box'][k][0]) for c in checked['physical_cover']); hi=max(Q(c['box'][k][1]) for c in checked['physical_cover'])
            ratio=(hi-lo)/(Q(request['box'][k][1])-Q(request['box'][k][0]))
            assert ratio == Q(row['normalized_ratio']) == Q(result['widths'][k]['normalized_ratio'])
        assert checked['details']['complete_numeric_replay']
        assert result['retained_complete_outer_cover']==checked['physical_cover']
        assert all(x['exit_code']==0 and not x['timeout'] for x in result['executions'])
    def informative(result,directory):
        widths_exact(result,directory)
        assert max(Q(x['normalized_ratio']) for x in result['widths'].values()) == Q(17394377843899475,4611686018427387904)
        assert len(result['retained_complete_outer_cover'])==1 and result['execution_mode']=='FRESH_RUN'
    def finite(result,directory):
        widths_exact(result,directory)
        assert all(Q(x['normalized_ratio'])==1 for x in result['widths'].values())
        assert len(result['retained_complete_outer_cover'])==2 and '3/55' in result['explanation']
        assert result['native_reference_post_checker']['ordered_pairs']==4
    fresh('informative',status='CONDITIONAL_UNION_WIDTH_CERTIFIED',check=informative)
    fresh('finite-data',status='UNKNOWN_OUTER_COVER',check=finite)
    fresh('unsupported',status='MODEL_NOT_ADMITTED',check=lambda r,d: (not r['solver_called']) or (_ for _ in ()).throw(AssertionError('solver called')))
    record('saved',['show','--example','informative','--output',str(newpath('saved'))],status='CONDITIONAL_UNION_WIDTH_CERTIFIED',
           check=lambda r,d: (r['execution_mode']=='SAVED_RESULTS' and not r['solver_called'] and not (d/'producer.stdout').exists()) or (_ for _ in ()).throw(AssertionError('saved provenance')))
    record('recheck',['check','--run',str(newpath('informative')),'--output',str(newpath('recheck'))],status='CONDITIONAL_UNION_WIDTH_CERTIFIED')
    protected={str(p.relative_to(newpath('informative'))):digest(p) for p in newpath('informative').rglob('*') if p.is_file()}
    record('existing-output',['run','--example','informative','--output',str(newpath('informative'))],code=2)
    assert protected=={str(p.relative_to(newpath('informative'))):digest(p) for p in newpath('informative').rglob('*') if p.is_file()}

    request=json.loads((APP/'examples/informative.json').read_bytes())
    def supplied(name,value,code=2,status=None,check=None):
        path=out/'requests'/(name+'.json')
        path.write_bytes(value if isinstance(value,bytes) else (json.dumps(value,allow_nan=True)+'\n').encode())
        return record(name,['run','--request',str(path),'--output',str(newpath(name))],code=code,status=status,check=check)
    supplied('malformed',b'{broken')
    supplied('top-list',b'[]')
    supplied('duplicate-key',b'{"model":"x","model":"y"}')
    supplied('nan',b'{"model":NaN}')
    supplied('float',b'{"model":0.25}')
    supplied('oversized',b' '*65537)
    supplied('nesting',b'['*1200+b'0'+b']'*1200)
    mutations=[('missing-feature',lambda r:r['features'].pop('AA1')),('reversed-interval',lambda r:r['features'].update(AA1=['1','0'])),
               ('out-of-range',lambda r:r['features'].update(AA1=['-1','1'])),('zero-denominator',lambda r:r['features'].update(AA1=['1/0','1'])),
               ('huge-rational',lambda r:r['features'].update(AA1=['0','1/'+'9'*79])),('integer-endpoint',lambda r:r['features'].update(AA1=[0,1])),
               ('boolean-budget',lambda r:r['budget'].update(max_stages=True)),('over-budget',lambda r:r['budget'].update(max_stages=65)),
               ('zero-states',lambda r:r['budget'].update(max_states=0)),('missing-budget',lambda r:r['budget'].pop('wall_ms')),
               ('extra-field',lambda r:r.update(extra='x'))]
    for name,mutation in mutations:
        r=copy.deepcopy(request);mutation(r);supplied(name,r)
    for name,mutation in [('wrong-model',lambda r:r.update(model='marker-alignment')),('wrong-schema',lambda r:r.update(schema='x')),
                          ('wrong-domain',lambda r:r['box'].update(rA=['1','2'])),('wrong-target',lambda r:r['normalized_width_targets'].update(rA='1/10'))]:
        r=copy.deepcopy(request);mutation(r);supplied(name,r,code=0,status='MODEL_NOT_ADMITTED')
    r=copy.deepcopy(request);r['budget'].update(max_stages=0,recovery_max_stages=0)
    supplied('zero-stages',r,code=0,status='UNKNOWN_OUTER_COVER',check=lambda r,d: widths_exact(r,d))
    r=copy.deepcopy(request);r['budget'].update(wall_ms=0,recovery_wall_ms=0)
    supplied('zero-wall',r,code=0,status='RECOVERED_UNKNOWN',check=lambda r,d: all(Q(x['normalized_ratio'])==1 for x in r['widths'].values()) or (_ for _ in ()).throw(AssertionError('resource fallback narrowed')))
    r=copy.deepcopy(request);r['features']={k:['0','1'] for k in r['features']}
    supplied('uninformative-boundary',r,code=0,status='UNKNOWN_OUTER_COVER',check=lambda r,d: widths_exact(r,d))
    link=out/'requests/symlink.json';link.symlink_to(APP/'examples/informative.json')
    record('symlink-request',['run','--request',str(link),'--output',str(newpath('symlink-request'))],code=2)

    def cloned(name):
        target=newpath(name);shutil.copytree(newpath('informative'),target);return target
    def fallback(result,directory):
        assert not result['original_complete_checker']['details'].get('complete_numeric_replay', False)
        assert all(Q(x['normalized_ratio'])==1 for x in result['widths'].values())
    damaged=cloned('tamper-journal');last=sorted((damaged/'journal').glob('state-*.json'))[-1]
    body=json.loads(last.read_bytes());body['frontier'][0]['state']['physical']['rA']=['1','1'];last.write_text(json.dumps(body))
    record('tamper-journal-check',['check','--run',str(damaged),'--output',str(newpath('tamper-journal-check'))],status='RECOVERED_UNKNOWN',check=fallback)
    damaged=cloned('missing-frame');frames=sorted((damaged/'journal').glob('state-*.json'));frames[len(frames)//2].unlink()
    record('missing-frame-check',['check','--run',str(damaged),'--output',str(newpath('missing-frame-check'))],status='RECOVERED_UNKNOWN',check=fallback)
    damaged=cloned('semantic-forgery');last=sorted((damaged/'journal').glob('state-*.json'))[-1]
    body=json.loads(last.read_bytes());body['frontier'][0]['state']['physical']['rA']=['1','1']
    forged=(json.dumps(body,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode()
    sequence=last.name.split('-')[1];last.unlink()
    (damaged/'journal'/('state-'+sequence+'-'+hashlib.sha256(forged).hexdigest()+'.json')).write_bytes(forged)
    record('semantic-forgery-check',['check','--run',str(damaged),'--output',str(newpath('semantic-forgery-check'))],status='RECOVERED_UNKNOWN',check=fallback)
    damaged=cloned('tamper-request');body=json.loads((damaged/'REQUEST.json').read_bytes());body['features']['AA1']=['1/2','1'];(damaged/'REQUEST.json').write_text(json.dumps(body))
    record('tamper-request-check',['check','--run',str(damaged),'--output',str(newpath('tamper-request-check'))],code=2)
    damaged=cloned('tamper-source');source=next((damaged/'runtime').rglob('global_engine.py'));source.chmod(0o644);source.write_bytes(source.read_bytes()+b'\n# changed\n')
    record('tamper-source-check',['check','--run',str(damaged),'--output',str(newpath('tamper-source-check'))],code=2)
    damaged=cloned('journal-exhaustion')
    for i in range(513): (damaged/'journal'/('state-extra-'+str(i)+'.json')).write_bytes(b'{}')
    record('journal-exhaustion-check',['check','--run',str(damaged),'--output',str(newpath('journal-exhaustion-check'))],code=2)
    record('missing-native',['run','--example','finite-data','--native-binary',str(out/'NO-BINARY'),'--output',str(newpath('missing-native'))],status='UNKNOWN_OUTER_COVER',
           check=lambda r,d: (widths_exact(r,d), (_ for _ in ()).throw(AssertionError('missing diagnostic failure')) if r['native_reference_post_checker']['status']!='DIAGNOSTIC_FAILED' else None))
    if a.native_binary:
        def native_check(result,directory):
            widths_exact(result,directory);diag=result['native_reference_post_checker']
            assert diag['status']=='COMPATIBILITY_PASS' and diag['exact_fields_match'] and diag['native_called']
            assert diag['ordered_pairs']==4 and diag['all_complete_cover_cells_consumed']==2
            assert all(x['status']=='UNKNOWN' for x in diag['native_actual'])
        record('native-full-path',['run','--example','finite-data','--native-binary',str(a.native_binary.absolute()),'--output',str(newpath('native-full-path'))],status='UNKNOWN_OUTER_COVER',check=native_check)
    def molecular_check(result,directory):
        request=json.loads((directory/'REQUEST.json').read_bytes())
        assert set(request['sequence_scenarios'])=={'REF','A','B','AB'}
        assert len({len(x) for x in request['sequence_scenarios'].values()})==1
        assert result['evidence']=='MOCK_SYNTHETIC' and result['execution_mode']=='FRESH_OFFLINE_FIXTURE_COMPUTATION'
        assert {x['family'] for x in result['interactions'].values()}=={'expression','splice_usage','polyadenylation'}
        assert all(x['evidence']=='MOCK_SYNTHETIC' for x in result['interactions'].values())
    record('molecular-full-path',['molecular','--output',str(newpath('molecular-full-path'))],status='SUCCESS',check=molecular_check)
    # Exercise example and saved-receipt claim integrity in a private test copy.
    # This does not edit the reviewed production tree.
    sandbox=out/'claim-integrity';(sandbox/'applications').mkdir(parents=True)
    copied_app=sandbox/'applications/practical-solver';shutil.copytree(APP,copied_app)
    (sandbox/'research').symlink_to(ROOT/'research',target_is_directory=True)
    saved_cli=list(CLI);CLI[2]=str(copied_app/'run.py')
    (copied_app/'examples/finite-data.json').write_text(json.dumps(request))
    record('example-identity-tamper',['run','--example','finite-data','--output',str(newpath('example-identity-tamper'))],code=2)
    shutil.copyfile(APP/'examples/finite-data.json',copied_app/'examples/finite-data.json')
    manifest=json.loads((copied_app/'SOURCE-IDENTITIES.json').read_bytes());manifest['engine_directory']='changed'
    (copied_app/'SOURCE-IDENTITIES.json').write_text(json.dumps(manifest))
    record('source-manifest-tamper',['run','--example','informative','--output',str(newpath('source-manifest-tamper'))],code=1)
    CLI[:]=saved_cli
    after={str(p.relative_to(ROOT)):digest(p) for p in reviewed_paths}
    final=dict(status='PASS' if all(r['passed'] for r in results) and source_before==after else 'FAILED',cases=results,
               passed=sum(r['passed'] for r in results),total=len(results),source_before=source_before,source_after=after,
               production_sources_unchanged=source_before==after,python=sys.version,
               verification_scope='independent execution and adversarial CLI tests; no empirical sampling-law or universal correctness proof')
    (out/'RESULTS.json').write_text(json.dumps(final,indent=2)+'\n')
    print(json.dumps(dict(status=final['status'],passed=final['passed'],total=final['total'])),flush=True)
    return 0 if final['status']=='PASS' else 1


if __name__=='__main__':
    raise SystemExit(main())
