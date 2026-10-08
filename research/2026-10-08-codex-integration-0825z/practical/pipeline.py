"""Reusable original-D numerical producer/checker and native post-checker CLI.

Only the declared fixed-six-copy clock-JC nine-parameter query is supported.
The native stage is an exact pair diagnostic; it never changes the cover or
promotes statistical/source admission. External applications must provide a
proper model-specific observation-to-request adapter before using this CLI.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import time
from types import ModuleType

PACKET=Path(__file__).resolve().parent
MODEL='fixed-six-copy-clock-jc-nine-v1'
SCHEMA='global-triangular-request-v1'
RUNNER_SHA='c901ec815c558990d87ce5ebbbbbef414b27b99a609228e6acefd9b0a908a509'
COMPARATOR_SHA='0ee32b5d0a72fb1fbe426cde97dd018d009e4b8dee0e63e057d6e3d9cb93598c'


def load(name,path,expected):
    # Execute only the single buffer that was actually authenticated. This
    # does not consult timestamp-valid pyc files or reread source for exec.
    if path.is_symlink() or path.stat().st_size>256*2**10:
        raise ValueError('bounded nonsymlink helper source required')
    raw=path.read_bytes()
    if len(raw)>256*2**10 or sha(raw)!=expected:
        raise ValueError('helper source identity mismatch: '+str(path))
    identity={'path':str(path),'sha256':sha(raw),'bytes':len(raw),
              'execution':'compile_exec_verified_single_read_bytes'}
    module=ModuleType(name);module.__file__=str(path);sys.modules[name]=module
    exec(compile(raw,module.__file__,'exec',dont_inherit=True),module.__dict__)
    module.__executed_source_identity__=identity
    return module


def sha(raw):return hashlib.sha256(raw).hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--request',type=Path,required=True)
    p.add_argument('--request-sha256',required=True)
    p.add_argument('--runtime-root',type=Path,required=True)
    p.add_argument('--staging-receipt',type=Path,required=True)
    p.add_argument('--native-binary',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();out=a.output.absolute();out.mkdir(parents=True,exist_ok=False)
    started=time.time();input_path=a.request.resolve()
    if input_path.stat().st_size>8*2**20:raise ValueError('bounded request size exceeded')
    raw=input_path.read_bytes()
    if sha(raw)!=a.request_sha256:raise ValueError('external request hash mismatch')
    request=json.loads(raw)
    refused={'status':'MODEL_NOT_ADMITTED','required_model':MODEL,'required_schema':SCHEMA,
             'required_observations':'six phased A1,A2,B1,B2,C1,C2 copies; complete two-site same-genealogy loci',
             'required_law':'fixed one-pulse backward B-to-C, original rate ties and stationary homogeneous clock-JC',
             'source_feasibility_certified':False,'statistical_coverage_verified':False,
             'parameter_accuracy_released':False,'native_or_numerical_solver_called':False,
             'request_sha256':a.request_sha256}
    if request.get('model')!=MODEL or request.get('schema')!=SCHEMA or request.get('quantity')!='shifted_bernoulli_character_mean':
        refused['reason']='Observation/model mapping to the original solver has not been admitted.'
        (out/'RESULT.json').write_text(json.dumps(refused,indent=2,sort_keys=True)+'\n')
        print(json.dumps(refused,sort_keys=True));return 0
    runner=load('_cli_original_runner',PACKET/'run_original_pipeline.py',RUNNER_SHA)
    compare=load('_cli_signed_comparator',PACKET/'recovered/research/2026-10-08-cloud-rust-signed-probe-0122z/compare_signed.py',COMPARATOR_SHA)
    executed_helpers={name:module.__executed_source_identity__ for name,module in
                      [('original_runner',runner),('signed_comparator',compare)]}
    (out/'EXECUTED-HELPERS.json').write_text(json.dumps(executed_helpers,indent=2,sort_keys=True)+'\n')
    runtime=a.runtime_root.resolve();staging=json.loads(a.staging_receipt.read_bytes())
    before=runner.authenticate(staging,runtime)
    # Preserve the complete original domain and target. Any future support for
    # supplied priors needs its own admission rather than becoming this target.
    domain={k:(['1/32','1/8'] if k in ('h','u','v') else ['1/6','2/3'] if k=='g' else ['1/2','6'])
            for k in compare.PHYSICAL}
    if request['box']!=domain or request['normalized_width_targets']!={k:'1/20' for k in compare.PHYSICAL}:
        refused['reason']='This entry point retains the full original nine-parameter domain and target.'
        (out/'RESULT.json').write_text(json.dumps(refused,indent=2,sort_keys=True)+'\n')
        print(json.dumps(refused,sort_keys=True));return 0
    (out/'REQUEST.json').write_bytes(raw)
    req=out/'REQUEST.json';pins=out/'CHECKER-PINS.json';pins.write_bytes((runtime/'CHECKER-PINS.json').read_bytes())
    engine=runtime/staging['engine_directory'];journal=out/'journal'
    common=['--request',str(req),'--request-sha256',a.request_sha256,'--checkpoints',str(journal)]
    executions=[runner.command(out,'producer',[sys.executable,'-B',str(engine/'global_engine.py'),*common]),
                runner.command(out,'checker',[sys.executable,'-B',str(engine/'global_check.py'),*common,
                     '--source-pins',str(pins),'--source-pins-sha256',sha(pins.read_bytes()),'--normal'])]
    checked=json.loads((out/'checker.stdout').read_bytes())
    diag={'status':'UNKNOWN','declared_stage':'post_checker_complete_cover_pair_diagnostic',
          'changes_original_producer_or_cover':False,'source_feasibility_certified':False,
          'statistical_coverage_verified':False,'parameter_accuracy_released':False}
    if not checked.get('details',{}).get('complete_numeric_replay'):
        diag['refusal']='CHECKER_INCOMPLETE'
    elif len(checked['physical_cover'])>8:
        diag['refusal']='NATIVE_PAIR_BUDGET'
    elif not checked['physical_cover']:
        diag['refusal']='EMPTY_COVER'
    else:
        recovered=PACKET/'recovered'
        frozen=json.loads((recovered/'research/2026-10-08-cloud-rust-signed-probe-0122z/FROZEN-SOURCES.json').read_bytes())
        source_before=compare.source_state(recovered,frozen)
        reference=compare.load_reference(recovered);binary=a.native_binary.resolve();binary_before=sha(binary.read_bytes())
        cases=[]
        for i,left in enumerate(checked['physical_cover']):
            for j,right in enumerate(checked['physical_cover']):
                cases.append({'id':f'pair_{i}_{j}','means0':request['features'],'means1':request['features'],
                    'physical0':left['box'],'physical1':right['box'],'precision':96,'max_bits':4096,'max_exp_calls':24})
        expected=[reference.receive(recovered,c['means0'],c['means1'],c['physical0'],c['physical1'],
                           c['precision'],c['max_bits'],c['max_exp_calls']) for c in cases]
        lines=compare.run_native(binary,('\n'.join(compare.row(c) for c in cases)+'\n').encode('ascii'),out,'native-pairs')
        actual=[compare.parse_native(line,c) for c,line in zip(cases,lines)]
        matches=len(lines)==len(cases) and all(x==compare.project_reference(y) for x,y in zip(actual,expected))
        identities_unchanged=source_before==compare.source_state(recovered,frozen) and binary_before==sha(binary.read_bytes())
        diag.update(status='COMPATIBILITY_PASS' if matches and identities_unchanged else 'UNKNOWN',
                    all_complete_cover_cells_consumed=len(checked['physical_cover']),ordered_pairs=len(cases),
                    cases=cases,python_expected=expected,native_actual=actual,exact_fields_match=matches,
                    source_and_binary_unchanged=identities_unchanged,binary_sha256=binary_before,
                    conditional_pair_geometry_all_pass=all(x['status']=='CONDITIONAL_PAIR_WIDTH_CERTIFIED' for x in actual))
        (out/'NATIVE-DIAGNOSTIC.json').write_text(json.dumps(diag,indent=2,sort_keys=True)+'\n')
    after=runner.authenticate(staging,runtime)
    result={'schema':'integration_practical_cli_result_v1','status':checked['status'],
            'original_complete_checker':checked,'executions':executions,'native_post_checker':diag,
            'original_source_bytes_unchanged':before==after,'request_sha256':a.request_sha256,
            'executed_helper_sources':executed_helpers,
            'program_sha256':sha(Path(__file__).read_bytes()),'started_unix':started,'ended_unix':time.time(),
            'original_full_D_and_nine_targets':True,'source_feasibility_certified':False,
            'statistical_coverage_verified':False,'parameter_accuracy_released':False,
            'native_receiver_is_not_original_producer_backend':True}
    (out/'RESULT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':result['status'],'normalized_union_widths':{k:v['normalized_ratio'] for k,v in checked['widths'].items()},
                      'native_exact_fields_match':diag.get('exact_fields_match'),
                      'native_conditional_pair_geometry_all_pass':diag.get('conditional_pair_geometry_all_pass'),
                      'statistical_coverage_verified':False,'parameter_accuracy_released':False},sort_keys=True))
    return 0


if __name__=='__main__':raise SystemExit(main())
