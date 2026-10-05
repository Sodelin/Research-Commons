"""Read-only frozen-control checks, including complete augmented planted-source enclosures."""
import json
from decimal import Decimal
from fractions import Fraction as F
from pathlib import Path
import seq_engine as e
import interval_math as m
import joint_contractor as ops
BASE=Path(__file__).resolve().parent
MANIFEST_SHA='8fde151f682c5b73b185895c304a9507a41b83aa6f385f5aa0c1383229a0b249'

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

def physical_metrics(request,cover):
    widths={};bounds={}
    if cover:
        for key in ops.PHYSICAL:
            low=min(F(cell['box'][key][0]) for cell in cover);high=max(F(cell['box'][key][1]) for cell in cover);width=high-low;original=request['physical'][key].width
            bounds[key]=[str(low),str(high)];widths[key]={'original':str(original),'final':str(width),'strictly_narrowed':width<original,'final_over_original':str(width/original) if original>0 else None}
    return {'physical_union_bounds':bounds if cover else None,'coordinate_widths':widths,'strictly_narrowed_coordinates':sum(item['strictly_narrowed'] for item in widths.values()),'all_nine_physically_contracted':len(widths)==9 and all(item['strictly_narrowed'] for item in widths.values()),'original_physical_union_sup_diameter':str(max(value.width for value in request['physical'].values()))}

def summarize():
    generated=BASE/'declared-requests';manifest=e.read_json(generated/'CONTROL-MANIFEST.json',MANIFEST_SHA);truth=e.read_json(generated/'TRUTH-FIXTURES.json',manifest['truth_sha256']);results=[]
    for entry in manifest['controls']:
        folder=BASE/'controls'/entry['name'];terminal=receipt(folder/'TERMINAL.json');inventory(folder,terminal)
        if not terminal['source_and_input_pins_stable'] or not terminal['checker_output_available'] or terminal['request_sha256']!=entry['sha256']:raise ValueError('invalid execution/recovery evidence')
        request=e.read_request(folder/'REQUEST.json',entry['sha256']);result=e.read_json(folder/'checker.stdout',terminal['inventory']['checker.stdout']['sha256'])
        if result['ranked_histories'] is not None or result['recommended_history'] is not None or result['parameter_accuracy_released'] or result['statistical_coverage_verified']:raise ValueError('unsupported release claim')
        counts={name:0 for name in entry['truth_ids']};unresolved=[];geometry=True;snapshots=0;last=None
        for checkpoint in sorted((folder/'checkpoints').glob('state-*.json')):
            payload=e.read_json(checkpoint,terminal['inventory'][str(checkpoint.relative_to(folder))]['sha256']);last=payload;snapshots+=1
            for name in entry['truth_ids']:
                status=truth_status(payload['frontier'],truth['physical'][name],truth['verified_raw_moments_128'][name])
                if status=='CERTIFIED_AUGMENTED_CONTAINMENT':counts[name]+=1
                else:unresolved.append({'checkpoint':checkpoint.name,'source':name,'status':status})
            if entry['name'] in ('uninformative','zero_preconditioner','zero_budget'):geometry=geometry and uninformative_geometry(payload,request)
        final_truth={name:truth_status(result['augmented_states'],truth['physical'][name],truth['verified_raw_moments_128'][name]) for name in entry['truth_ids']}
        preconditions={};unsupported=[]
        for event in last['events'] if last is not None else []:
            detail=event.get('detail',{});detail=detail.get('operator_detail',detail)
            if isinstance(detail,dict) and 'preconditioner_mode' in detail:
                key=detail['preconditioner_mode'];preconditions[key]=preconditions.get(key,0)+1
                if detail['auxiliary_or_target_clipping_used_for_Fq_or_J'] or detail['target_units']!='raw_laplace_moments':raise ValueError('Jacobian-domain/target violation')
            if event['kind']=='unsupported':unsupported.append(event['detail'])
        results.append({'name':entry['name'],'domain_scope':entry['domain_scope'],'status':result['status'],'mode':result['mode'],'retained_states':len(result['physical_cover']),'snapshots':snapshots,'certified_augmented_containment_counts':counts,'unresolved_containment_checks':unresolved,'final_truth_checks':final_truth,'full_original_domain_check':geometry if entry['name'] in ('uninformative','zero_preconditioner','zero_budget') else None,**physical_metrics(request,result['physical_cover']),'physical_union_sup_diameter':result['physical_union_sup_diameter'],'physical_cell_mesh':result['physical_cell_mesh'],'preconditioner_modes':preconditions,'unsupported_operations':unsupported,'details':result['details'],'terminal_sha256':e.sha((folder/'TERMINAL.json').read_bytes()),'checker_output_sha256':terminal['inventory']['checker.stdout']['sha256']})
    return {'schema':'coherent-joint-arithmetic-control-results-v1','controls':results,'statistical_coverage_claimed':False,'parameter_accuracy_released':False,'ranked_histories':None,'new_parameter_vectors':False,'new_biological_data_or_simulation':False,'source_manifest_sha256':e.sha((BASE/'SOURCE-PINS.json').read_bytes()),'control_manifest_sha256':MANIFEST_SHA,'local_domains_are_supplied_not_globally_inferred':True}
if __name__=='__main__':print(json.dumps(summarize(),sort_keys=True,indent=2))
