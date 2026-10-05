"""Read-only frozen-control checks, including complete augmented planted-source enclosures."""
import json
from decimal import Decimal
from fractions import Fraction as F
from pathlib import Path
import seq_engine as e
import interval_math as m
import contractors as ops
BASE=Path(__file__).resolve().parent
PREPARATION_SHA='5e8dc3d126e0fee8d5921bf85f7bccd6092a03e5099a659946840de14244edb0'
MANIFEST_SHA='9a5c172900d6eaa96114b25da6c809ab659fe59a0e42bdda8d8cb1fb6c521c42'

def receipt(path,expected=None):
    p=Path(path)
    if p.is_symlink() or p.stat().st_size>e.MAX_JSON_BYTES:raise ValueError('receipt size/link')
    raw=p.read_bytes()
    if len(raw)>e.MAX_JSON_BYTES or expected is not None and e.sha(raw)!=expected:raise ValueError('receipt identity')
    def reject(_):raise ValueError('nonfinite receipt number')
    return json.loads(raw,object_pairs_hook=e.legacy.no_duplicates,parse_float=Decimal,parse_constant=reject)

def inventory(folder,terminal):
    for name,item in terminal['inventory'].items():
        p=folder/name
        if p.is_symlink() or p.stat().st_size!=item['bytes'] or e.sha(p.read_bytes())!=item['sha256']:raise ValueError('original inventory mismatch')

def truth_status(frontier,point,raw):
    point={key:F(value) for key,value in point.items()};aux={'A':point['h']+point['u'],'T':point['h']+point['u']+point['v'],'L':point['u']+point['v']};physical_match=False
    for cell in frontier:
        state=cell['state']
        if not all(F(state['physical'][key][0])<=value<=F(state['physical'][key][1]) for key,value in point.items()):continue
        if not all(F(state['aux'][key][0])<=value<=F(state['aux'][key][1]) for key,value in aux.items()):continue
        physical_match=True
        if all(F(state['moments'][key][0])<=F(raw[key]['lower'])<=F(raw[key]['upper'])<=F(state['moments'][key][1]) for key in m.FEATURES):return 'CERTIFIED_AUGMENTED_CONTAINMENT'
    return 'UNRESOLVED_128BIT_MOMENT_CONTAINMENT' if physical_match else 'PLANTED_PHYSICAL_OR_AUXILIARY_POINT_ABSENT'

def uninformative_geometry(payload,request):
    physical={key:[str(value.lo),str(value.hi)] for key,value in request['physical'].items()};boxes={'r':physical}
    for event in payload['events']:
        if event['kind']=='split':
            parent=boxes.pop(event['cell']);axis=event['axis'];mid=(F(parent[axis][0])+F(parent[axis][1]))/2
            for suffix,bounds in [('0',[parent[axis][0],str(mid)]),('1',[str(mid),parent[axis][1]])]:boxes[event['cell']+suffix]={**parent,axis:bounds}
        elif event['kind']=='excluded':return False
    return set(boxes)=={cell['id'] for cell in payload['frontier']} and all(cell['state']['physical']==boxes[cell['id']] for cell in payload['frontier'])

def summarize():
    preparation=BASE/'fixture-preparation-attempt1';prep=receipt(preparation/'TERMINAL.json',PREPARATION_SHA);inventory(preparation,prep)
    generated=preparation/'generated';manifest=e.read_json(generated/'CONTROL-MANIFEST.json',MANIFEST_SHA);truth=e.read_json(generated/'TRUTH-FIXTURES.json',manifest['truth_sha256']);results=[]
    for entry in manifest['controls']:
        folder=BASE/'controls'/entry['name'];terminal=receipt(folder/'TERMINAL.json');inventory(folder,terminal)
        if not terminal['source_and_input_pins_stable'] or not terminal['checker_output_available'] or terminal['request_sha256']!=entry['sha256']:raise ValueError('invalid completed/recovered evidence')
        request=e.read_request(folder/'REQUEST.json',entry['sha256']);result=e.read_json(folder/'checker.stdout',terminal['inventory']['checker.stdout']['sha256'])
        if result['ranked_histories'] is not None or result['recommended_history'] is not None or result['parameter_accuracy_released'] or result['statistical_coverage_verified']:raise ValueError('unsupported release')
        counts={name:0 for name in entry['truth_ids']};unresolved=[];geometry=True;snapshots=0
        for checkpoint in sorted((folder/'checkpoints').glob('state-*.json')):
            relative=str(checkpoint.relative_to(folder));payload=e.read_json(checkpoint,terminal['inventory'][relative]['sha256']);snapshots+=1
            for name in entry['truth_ids']:
                status=truth_status(payload['frontier'],truth['physical'][name],truth['verified_raw_moments_128'][name])
                if status=='CERTIFIED_AUGMENTED_CONTAINMENT':counts[name]+=1
                else:unresolved.append({'checkpoint':checkpoint.name,'source':name,'status':status})
            if entry['name']=='uninformative':geometry=geometry and uninformative_geometry(payload,request)
        final_truth={name:truth_status(result['augmented_states'],truth['physical'][name],truth['verified_raw_moments_128'][name]) for name in entry['truth_ids']}
        cover=result['physical_cover'];bounds={key:[str(min(F(cell['box'][key][0]) for cell in cover)),str(max(F(cell['box'][key][1]) for cell in cover))] for key in ops.PHYSICAL} if cover else None
        results.append({'name':entry['name'],'status':result['status'],'mode':result['mode'],'retained_states':len(cover),'snapshots':snapshots,'certified_augmented_containment_counts':counts,'final_truth_checks':final_truth,'unresolved_containment_checks':unresolved,'uninformative_full_original_domain_check':geometry if entry['name']=='uninformative' else None,'physical_union_bounds':bounds,'physical_union_sup_diameter':result['physical_union_sup_diameter'],'physical_cell_mesh':result['physical_cell_mesh'],'details':result['details'],'terminal_sha256':e.sha((folder/'TERMINAL.json').read_bytes()),'checker_output_sha256':terminal['inventory']['checker.stdout']['sha256']})
    return {'schema':'sequential-arithmetic-control-results-v1','controls':results,'all_nine_unknown_parameters_preserved':True,'statistical_coverage_claimed':False,'parameter_accuracy_released':False,'ranked_histories':None,'new_biological_data_or_simulation':False,'source_manifest_sha256':e.sha((BASE/'SOURCE-PINS.json').read_bytes()),'control_manifest_sha256':MANIFEST_SHA}
if __name__=='__main__':print(json.dumps(summarize(),sort_keys=True,indent=2))
