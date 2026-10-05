"""One-realization authenticated readout; no repeated-coverage estimate."""
import json
from decimal import Decimal
from fractions import Fraction as F
from pathlib import Path
import integration_core as c
import evaluate_truth as truth
BASE=Path(__file__).resolve().parent
COMPOSITION_MANIFEST_SHA='f13128d7c6e523c0346220611983c670d11bfc8f270451ebaecea0b87e440a54'
MANIFEST_SHA='e7fdade296d0dd8653ed9ffc1b12ba64ad186b80b94b3d6108eec4caf352c9f0'
def receipt(path):
    p=Path(path)
    if p.is_symlink() or p.stat().st_size>c.MAX_BYTES:raise ValueError('receipt resource/link')
    def reject(_):raise ValueError('nonfinite')
    return json.loads(p.read_bytes(),object_pairs_hook=c.no_duplicates,parse_float=Decimal,parse_constant=reject)
def inventory(folder,t):
    for name,item in t['inventory'].items():
        rel=Path(name)
        if rel.is_absolute() or '..' in rel.parts:raise ValueError('unsafe inventory')
        p=folder/rel
        if p.is_symlink() or p.stat().st_size!=item['bytes'] or c.sha(p.read_bytes())!=item['sha256']:raise ValueError('inventory mismatch')
def mean_status(means,box):
    if any(F(means[k]['upper'])<F(box[k][0]) or F(box[k][1])<F(means[k]['lower']) for k in c.FEATURES):return 'CERTIFIED_OUTSIDE'
    if all(F(box[k][0])<=F(means[k]['lower'])<=F(means[k]['upper'])<=F(box[k][1]) for k in c.FEATURES):return 'CERTIFIED_INSIDE'
    return 'UNRESOLVED_FINITE_ENCLOSURE'
def truth_status(frontier,point,raw):
    point={key:F(value) for key,value in point.items()};aux={'A':point['h']+point['u'],'T':point['h']+point['u']+point['v'],'L':point['u']+point['v']};physical_match=False
    for cell in frontier:
        state=cell['state']
        if not all(F(state['physical'][key][0])<=value<=F(state['physical'][key][1]) for key,value in point.items()):continue
        if not all(F(state['aux'][key][0])<=value<=F(state['aux'][key][1]) for key,value in aux.items()):continue
        physical_match=True
        if all(F(state['moments'][key][0])<=F(raw[key]['lower'])<=F(raw[key]['upper'])<=F(state['moments'][key][1]) for key in c.FEATURES):return 'CERTIFIED_AUGMENTED_CONTAINMENT'
    return 'UNRESOLVED_128BIT_MOMENT_CONTAINMENT' if physical_match else 'PLANTED_PHYSICAL_OR_AUXILIARY_POINT_ABSENT'

def summarize():
    old=c.read(BASE/'initial-source/SOURCE-PINS.json',COMPOSITION_MANIFEST_SHA)
    for name,pin in old['sources'].items():
        if c.sha((BASE/'initial-source'/name).read_bytes())!=pin:raise ValueError('original composition source evidence changed')
    declared=BASE/'declared-model';manifest=c.read(declared/'CONTROL-MANIFEST.json',MANIFEST_SHA)
    folder=BASE/'composition-attempt1';t=receipt(folder/'TERMINAL.json');inventory(folder,t)
    if t['error'] or t['output_failure'] or t['inventory_failure'] or t['data_confidence_certificate_issued'] or not t['fresh_inverse_verified']:raise ValueError('unaccepted composition terminal')
    if t['request_sha256']!=manifest['request_sha256'] or t['source_manifest_sha256']!=COMPOSITION_MANIFEST_SHA:raise ValueError('source/request identity')
    output=c.read(folder/'COMPOSED-RESULT.json',t['composed_output_sha256'])
    if output['admission_classification']!='synthetic_model_check' or output['data_confidence_certificate_eligible'] or output['data_confidence_certificate_issued'] or output['ranked_histories'] is not None or output['finite_generator_law_certified']:raise ValueError('model-check scope')
    req,delta=c.request(declared/'REQUEST.json',manifest['request_sha256']);data=c.read(declared/'DATASET.json',manifest['dataset_sha256'])
    counts=c.extract(data,req['expected_loci'],req['selection_sha256']);confidence=c.confidence(counts,delta,req['radius_steps']);inv=c.inverse_request(req,confidence,manifest['request_sha256'],c.sha(c.canonical(counts)),c.sha(c.canonical(confidence)))
    for name,obj in [('EXTRACTION.json',counts),('CONFIDENCE.json',confidence),('INVERSE-REQUEST.json',inv)]:
        if c.canonical(obj)!=(folder/'prepared'/name).read_bytes():raise ValueError('extraction/confidence/transformation mismatch')
    tf=BASE/'truth-attempt2';tt=receipt(tf/'TERMINAL.json');inventory(tf,tt)
    if tt['source_manifest_sha256']!=c.sha((BASE/'SOURCE-PINS.json').read_bytes()) or tt['error'] or not tt['pins_stable'] or tt['stage']['status']!='EXECUTION_EXIT_ZERO':raise ValueError('truth terminal')
    values=c.read(tf/'TRUTH.json',tt['inventory']['TRUTH.json']['sha256'])
    if values['physical_truth']!=truth.TRUTH or values['bits']!=128 or values['observed_data_read'] or values['generation_receipt_sha256']!=c.GENERATION_RECEIPT_SHA:raise ValueError('truth identity')
    means={k:values['forward']['features'][k[:-1]][int(k[-1])-1]['mean_interval'] for k in c.FEATURES};raw={k:values['forward']['features'][k[:-1]][int(k[-1])-1]['laplace_interval'] for k in c.FEATURES}
    inclusion=mean_status(means,confidence['shifted_mean_box']);snapshots=[]
    for path in sorted((folder/'journal').glob('state-*.json')):
        frame=c.read(path,t['inventory'][str(path.relative_to(folder))]['sha256']);snapshots.append({'commit':path.name,'truth_status':truth_status(frame['frontier'],truth.TRUTH,raw)})
    checked=c.read(folder/'checker.stdout',t['inventory']['checker.stdout']['sha256']);final=truth_status(checked['augmented_states'],truth.TRUTH,raw)
    import compose_run
    provider=c.load_provider();parsed=provider.read_request(folder/'prepared/INVERSE-REQUEST.json',output['inverse_request_sha256']);prep=c.read(folder/'prepared/PREPARATION.json',t['inventory']['prepared/PREPARATION.json']['sha256'])
    rebuilt=compose_run.report(prep,confidence,checked,parsed,provider)
    if any(output[k]!=v for k,v in rebuilt.items()):raise ValueError('composed field replay')
    if inclusion=='CERTIFIED_INSIDE' and final=='PLANTED_PHYSICAL_OR_AUXILIARY_POINT_ABSENT':raise ValueError('conditional truth containment failed; preserve without retry')
    return {'schema':'one-synthetic-model-check-readout-v1','status':output['status'],'dataset_sha256':manifest['dataset_sha256'],'counts':counts['counts'],'m':counts['m'],'delta':str(delta),'radius':confidence['radius'],'confidence_box':confidence['shifted_mean_box'],'ideal_truth_mean_box_status':inclusion,'truth_final_cover_status':final,'producer_snapshot_checks':snapshots,'producer_snapshot_scope':'particular known source only; not a substitute for mathematical replay','complete_numeric_replay':output['complete_numeric_replay'],'numerical_mode':output['numerical_mode'],'retained_boxes':len(output['physical_cover']),'widths':output['widths'],'whole_union_width_target_met':output['whole_union_width_target_met'],'generation_runs':1,'independent_realizations':1,'finite_program_law_certified':False,'data_confidence_certificate_issued':False,'repeated_coverage_estimated':False,'ranked_histories':None,'source_manifest_sha256':t['source_manifest_sha256'],'composition_terminal_sha256':c.sha((folder/'TERMINAL.json').read_bytes()),'truth_terminal_sha256':c.sha((tf/'TERMINAL.json').read_bytes()),'known_truth_output_sha256':tt['inventory']['TRUTH.json']['sha256']}
if __name__=='__main__':print(json.dumps(summarize(),sort_keys=True,indent=2))
