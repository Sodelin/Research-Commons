"""Reuse actual public 1,024-locus synthetic panels; no generation or admission.

Recount literal features, reproduce the historical fixed-block bands and run
the original full-D numerical pipeline. This retains ideal-model-only scope.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import importlib.util
import json
import sys
from types import ModuleType

PACKET=Path(__file__).resolve().parent
COMMONS=PACKET.parents[2]
SCRATCH=Path('/workspace/scratch/integration-practical')
SOURCE='research/2026-10-05-dot-msci-generated-phased-model-check-1854z'
PINS={
    'integration/integration_core.py':'f409f3ae1cfeb04db61f7b3b9f0aad76e18e372c57289463ad7d5622023b131e',
    'integration/declared-model/DATASET.json':'4ae2d541515bf87d1709d3708e74af9f2c2ac2ae35ed60d38456050b3ef60e03',
    'integration/composition-attempt1/ANALYSIS-REQUEST.json':'aebcfdfe2caa31d842f56be70387b415fc9f8677aa8f8cd4a58ea62b83c82f30',
    'integration/composition-attempt1/prepared/INVERSE-REQUEST.json':'a011e2369224bf4de82990be0eca622e8676c8d8d8addd9e1e757ac01f6a82f3',
    'integration/composition-attempt1/prepared/CONFIDENCE.json':'84fa51b6961b6f0e63eb5d6aa04f54c2914532285ab1ada4f8c42952915c2926',
    'integration/composition-attempt1/prepared/EXTRACTION.json':'89619327bfe8e8fb86c0b5e0792e9361ab3824a3ed4f0567858ffe6c65bc8ec7',
}
BUDGET={'scalar_steps':32,'max_stages':32,'max_splits':1,'max_states':2,'max_depth':1,
        'wall_ms':20000,'recovery_wall_ms':20000,'recovery_max_stages':32}


def sha(data):return hashlib.sha256(data).hexdigest()


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec)
    sys.modules[name]=m;spec.loader.exec_module(m);return m


def main():
    attempt=PACKET/'finite-data';attempt.mkdir(exist_ok=False)
    runner=load('_finite_original_runner',PACKET/'run_original_pipeline.py')
    runtime=SCRATCH/'jc-original';engine=runtime/'msci-ab-profile-implementation-20261005-1612z'
    staging=json.loads((PACKET/'original-multistage/STAGING.json').read_bytes())
    before=runner.authenticate(staging,runtime)
    raw={}
    for rel,digest in PINS.items():
        data=(COMMONS/SOURCE/rel).read_bytes()
        if sha(data)!=digest:raise RuntimeError('public finite-input identity '+rel)
        raw[rel]=data
    module=ModuleType('_authenticated_original_literal_extractor')
    module.__file__=str(COMMONS/SOURCE/'integration/integration_core.py');sys.modules[module.__name__]=module
    exec(compile(raw['integration/integration_core.py'],module.__file__,'exec',dont_inherit=True),module.__dict__)
    analysis=json.loads(raw['integration/composition-attempt1/ANALYSIS-REQUEST.json'])
    data=json.loads(raw['integration/declared-model/DATASET.json'])
    extraction=module.extract(data,analysis['expected_loci'],analysis['selection_sha256'])
    old_extraction=json.loads(raw['integration/composition-attempt1/prepared/EXTRACTION.json'])
    if extraction!=old_extraction:raise RuntimeError('literal recount changed')
    sys.path.insert(0,str(engine));import global_engine as original_engine
    confidence=module.confidence(extraction,F(analysis['delta']),analysis['radius_steps'],
                                 exp_neg=original_engine.m.forward.exp_neg)
    old_confidence=json.loads(raw['integration/composition-attempt1/prepared/CONFIDENCE.json'])
    if confidence!=old_confidence:raise RuntimeError('fixed-block band reproduction changed')
    request=json.loads(raw['integration/composition-attempt1/prepared/INVERSE-REQUEST.json'])
    if request['features']!=confidence['shifted_mean_box']:raise RuntimeError('observation-to-request changed')
    request['budget']=dict(BUDGET)
    request['provenance'].update(isolated_replay='20261008_integration_existing_literal_record',
                                 fresh_data=False,statistical_coverage_claimed=False,
                                 classification='synthetic_model_check',finite_program_law_certified=False,
                                 confidence_eligibility=False,confidence_certificate_issued=False)
    request_raw=runner.canonical(request);request_sha=sha(request_raw)
    req=attempt/'REQUEST.json';req.write_bytes(request_raw)
    (attempt/'EXTRACTION.json').write_text(json.dumps(extraction,indent=2,sort_keys=True)+'\n')
    (attempt/'CONFIDENCE.json').write_text(json.dumps(confidence,indent=2,sort_keys=True)+'\n')
    pins=attempt/'CHECKER-PINS.json';pins.write_bytes((runtime/'CHECKER-PINS.json').read_bytes());pin_sha=sha(pins.read_bytes())
    # Y=(1+character product)/2 gives E[character product]=2E[Y]-1.
    # The original stationary clock-JC model makes the k-site character
    # expectation the pair Laplace value at 8k/3. Intersect with [0,1] once.
    typed=original_engine.read_request(req,request_sha);initialized=original_engine.initial_cell(typed)
    expected={key:[str(max(F(0),2*F(lo)-1)),str(min(F(1),2*F(hi)-1))]
              for key,(lo,hi) in confidence['shifted_mean_box'].items()}
    actual={key:[str(value.lo),str(value.hi)] for key,value in initialized['state']['moments'].items()}
    example=original_engine.ops.initial(typed['physical'],{key:original_engine.m.I(F(3,4),F(7,8))
                                                        for key in original_engine.ops.FEATURES})
    if actual!=expected or any([v.lo,v.hi]!=[F(1,2),F(3,4)] for v in example['moments'].values()):
        raise RuntimeError('once-only shifted-mean conversion changed')
    (attempt/'MEAN-CONVERSION.json').write_text(json.dumps({'formula':'raw = clip_to_[0,1](2*shifted-1)',
                'literal_bernoulli_definition':'Y=(1+product_of_selected_chi)/2',
                'clock_JC_laplace_argument':'8*k/3','conversion_count':1,'actual':actual,'expected':expected,
                'example_shifted':['3/4','7/8'],'example_raw':['1/2','3/4'],'all_nine_matches':True},indent=2,sort_keys=True)+'\n')
    journal=attempt/'journal';common=['--request',str(req),'--request-sha256',request_sha,'--checkpoints',str(journal)]
    executions=[runner.command(attempt,'producer',[sys.executable,'-B',str(engine/'global_engine.py'),*common]),
                runner.command(attempt,'checker',[sys.executable,'-B',str(engine/'global_check.py'),*common,
                                  '--source-pins',str(pins),'--source-pins-sha256',pin_sha,'--normal'])]
    producer=json.loads((attempt/'producer.stdout').read_bytes());checker=json.loads((attempt/'checker.stdout').read_bytes())
    archive_path=COMMONS/'research/2026-10-07-cloud-practical-1619z/covariance-points-attempt1/RESULT.json'
    archive=archive_path.read_bytes()
    if sha(archive)!='8acf47eadbb01e220f9ebb87746b64f070a0f527bfc0a230e58b316e9f3c6931':raise RuntimeError('pair source identity')
    saved=json.loads(archive);points=saved['source_parameter_points'];means=saved['source_forward_mean_boxes']
    mean_contained=all(F(confidence['shifted_mean_box'][key][0])<=F(bounds[0])<=F(bounds[1])<=F(confidence['shifted_mean_box'][key][1])
                       for mean in means for key,bounds in mean.items())
    domain=request['box']
    points_admitted=all(F(domain[key][0])<=F(v[0])==F(v[1])<=F(domain[key][1]) for point in points for key,v in point.items())
    separation=abs(F(points[0]['rA'][0])-F(points[1]['rA'][0]))/(F(domain['rA'][1])-F(domain['rA'][0]))
    witness={'source_mean_archive_sha256':sha(archive),'all_nine_source_mean_enclosures_inside_actual_fixed_block_bands':mean_contained,
             'two_points_inside_original_D':points_admitted,'source_parameter_points':points,
             'normalized_rA_separation':str(separation),'requested_target':'1/20',
             'exact_candidate_set_width_target_impossible_for_this_band':mean_contained and points_admitted and separation>F(1,20),
             'scope':'this fixed archived confidence box and original source; no impossibility claim for other estimators or future data'}
    (attempt/'PAIR-WIDTH-OBSTRUCTION.json').write_text(json.dumps(witness,indent=2,sort_keys=True)+'\n')
    result={'schema':'integration_practical_actual_public_finite_record_v1','classification':'synthetic_model_check',
            'status':checker['status'],'input_pins':PINS,'original_dataset_recounted':True,'loci':extraction['m'],
            'counts':extraction['counts'],'historical_bands_reproduced_exactly':True,'delta':analysis['delta'],
            'radius':confidence['radius'],'original_full_D_preserved':True,'request_budget':BUDGET,'executions':executions,
            'producer':producer,'checker':checker,'pair_width_obstruction':witness,
            'source_bytes_unchanged':before==runner.authenticate(staging,runtime),
            'finite_generator_law_certified':False,'observed_scientific_confidence_admitted':False,
            'parameter_accuracy_released':False,'fresh_data_generated':False,
            'journal':[{'name':p.name,'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
                       for p in sorted(journal.glob('state-*.json'))]}
    (attempt/'RESULT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    if not checker['details'].get('complete_numeric_replay'):raise RuntimeError('finite record complete replay pending')
    print(json.dumps({'status':checker['status'],'loci':1024,'radius':confidence['radius'],
                      'all_nine_normalized_union_widths':{k:v['normalized_ratio'] for k,v in checker['widths'].items()},
                      'pair_width_obstruction':witness['exact_candidate_set_width_target_impossible_for_this_band'],
                      'rA_pair_separation':str(separation),'complete_numeric_replay':True},sort_keys=True))


if __name__=='__main__':main()
