"""Actual one-stage baseline and explicitly post-checker native pair diagnostic.

The receiver consumes the actual independently checked complete cover. It
does not change the original producer, journal, exported cover or admission.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import importlib.util
import json
import sys
import time

PACKET=Path(__file__).resolve().parent
SCRATCH=Path('/workspace/scratch/integration-practical')


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec)
    sys.modules[name]=module;spec.loader.exec_module(module);return module


def main():
    pipeline=load('_integration_original_runner',PACKET/'run_original_pipeline.py')
    compare=load('_integration_signed_comparator',PACKET/'recovered/research/2026-10-08-cloud-rust-signed-probe-0122z/compare_signed.py')
    runtime=SCRATCH/'jc-original';engine=runtime/'msci-ab-profile-implementation-20261005-1612z'
    staging=json.loads((PACKET/'original-multistage/STAGING.json').read_bytes())
    before=pipeline.authenticate(staging,runtime)
    baseline=PACKET/'original-baseline';baseline.mkdir(exist_ok=False)
    request=runtime/'REQUEST.json';pins=runtime/'CHECKER-PINS.json'
    raw=request.read_bytes();request_sha=pipeline.sha(raw);pin_sha=pipeline.sha(pins.read_bytes())
    (baseline/'REQUEST.json').write_bytes(raw);(baseline/'CHECKER-PINS.json').write_bytes(pins.read_bytes())
    journal=baseline/'journal'
    common=['--request',str(request),'--request-sha256',request_sha,'--checkpoints',str(journal)]
    executions=[pipeline.command(baseline,'producer',[sys.executable,'-B',str(engine/'global_engine.py'),*common]),
                pipeline.command(baseline,'checker',[sys.executable,'-B',str(engine/'global_check.py'),*common,
                    '--source-pins',str(pins),'--source-pins-sha256',pin_sha,'--normal'])]
    checked=json.loads((baseline/'checker.stdout').read_bytes())
    result={'status':checked['status'],'checker':checked,'executions':executions,
            'request_sha256':request_sha,'all_source_bytes_unchanged':before==pipeline.authenticate(staging,runtime),
            'scope':'fresh one-stage original-D baseline, separate whole-journal checker'}
    (baseline/'RESULT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    if not checked['details'].get('complete_numeric_replay') or checked['widths']['rR']['normalized_ratio']!='1/256' or any(
          value['normalized_ratio']!='1' for key,value in checked['widths'].items() if key!='rR'):
        raise RuntimeError('fresh baseline differs; result preserved')

    destination=PACKET/'post-checker-native';destination.mkdir(exist_ok=False)
    started=time.time();recovered=PACKET/'recovered'
    frozen=json.loads((recovered/'research/2026-10-08-cloud-rust-signed-probe-0122z/FROZEN-SOURCES.json').read_bytes())
    source_before=compare.source_state(recovered,frozen)
    binary=SCRATCH/'signed-target/release/signed-nine-probe';binary_sha=pipeline.sha(binary.read_bytes())
    cases=[];bindings=[]
    for run in ('original-baseline','original-multistage'):
        folder=PACKET/run
        evidence=json.loads((folder/'checker.stdout').read_bytes())
        receipt=json.loads((folder/'checker.execution.json').read_bytes())
        if receipt['exit_code'] or receipt['timeout'] or receipt['stdout_sha256']!=pipeline.sha((folder/'checker.stdout').read_bytes()):
            raise RuntimeError('actual checker execution identity')
        if not evidence['details'].get('complete_numeric_replay') or evidence['statistical_coverage_verified'] or evidence['parameter_accuracy_released']:
            raise RuntimeError('checker completeness/admission changed')
        request_data=json.loads((folder/'REQUEST.json').read_bytes())
        if evidence['request_sha256']!=pipeline.sha((folder/'REQUEST.json').read_bytes()):raise RuntimeError('request binding')
        cover=evidence['physical_cover']
        bindings.append({'run':run,'checker_stdout_sha256':receipt['stdout_sha256'],
                         'request_sha256':evidence['request_sha256'],'complete_numeric_replay':True,
                         'all_cells_consumed':len(cover),'ordered_pairs':len(cover)**2,
                         'exported_union_widths':evidence['widths']})
        for i,left in enumerate(cover):
            for j,right in enumerate(cover):
                cases.append({'id':run.replace('-','_')+f'_{i}_{j}','means0':request_data['features'],
                       'means1':request_data['features'],'physical0':left['box'],'physical1':right['box'],
                       'precision':96,'max_bits':4096,'max_exp_calls':24})
    # Exact equality must remain UNKNOWN under the strict <1/20 receiver rule.
    archive=json.loads(compare.authenticated(recovered/compare.ARCHIVE,compare.ARCHIVE_SHA))
    strict=next(c for c in compare.fixture_cases(archive) if c['id']=='supplied_box_width_above')
    strict['id']='strict_target_equality';strict['physical0']['rA']=['1','51/40'];strict['physical1']['rA']=['1','51/40']
    cases.append(strict)
    reference=compare.load_reference(recovered)
    expected=[reference.receive(recovered,c['means0'],c['means1'],c['physical0'],c['physical1'],
                       c['precision'],c['max_bits'],c['max_exp_calls']) for c in cases]
    lines=compare.run_native(binary,('\n'.join(compare.row(c) for c in cases)+'\n').encode('ascii'),destination,'native')
    if len(lines)!=len(cases):raise RuntimeError('native count')
    actual=[compare.parse_native(line,c) for line,c in zip(lines,cases)]
    matches=[a==compare.project_reference(e) for a,e in zip(actual,expected)]
    boundary=actual[-1]
    strict_ok=boundary['status']=='UNKNOWN' and boundary['maximum_normalized_difference_bound']=='1/20'
    after=compare.source_state(recovered,frozen)
    report={'schema':'integration_practical_native_post_checker_pairs_v1',
            'status':'PASS' if all(matches) and strict_ok and source_before==after else 'UNKNOWN',
            'original_producer_consumes_native_receiver':False,'declared_integration':'post_checker_complete_cover_pair_diagnostic',
            'cover_or_journal_not_modified':True,'bindings':bindings,'cases':cases,'python_expected':expected,'native_actual':actual,
            'exact_matches':matches,'strict_equality_remains_unknown':strict_ok,'source_bytes_unchanged':source_before==after,
            'binary_sha256':binary_sha,'binary_bytes_unchanged':binary_sha==pipeline.sha(binary.read_bytes()),
            'started_unix':started,'ended_unix':time.time(),'forward_evaluations':0,'observation_rows':0,
            'source_feasibility_certified':False,'statistical_coverage_verified':False,'parameter_accuracy_released':False,
            'program_sources':{name:pipeline.sha((PACKET/name).read_bytes()) for name in
                              ('baseline_and_diagnostic.py','run_original_pipeline.py')}}
    (destination/'RESULT.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    if report['status']!='PASS':raise RuntimeError('post-checker diagnostic mismatch')
    print(json.dumps({'status':'PASS','fresh_baseline':checked['status'],'native_post_checker_pairs':len(cases)-1,
                      'strict_threshold_equality':boundary['status'],'cover_or_journal_modified':False}))


if __name__=='__main__':main()
