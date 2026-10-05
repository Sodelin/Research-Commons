"""Read-only frozen-control checks, including complete augmented planted-source enclosures."""
import json
from decimal import Decimal
from fractions import Fraction as F
from pathlib import Path
import global_engine as e
import interval_math as m
import global_contractors as ops
BASE=Path(__file__).resolve().parent
MANIFEST_SHA='e825e70d7b8462c63806c4cb58846c7d212df7e4767b59299deffb612533e8dc'

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

def summarize():
    inputs=BASE/'declared-requests';manifest=e.read_json(inputs/'CONTROL-MANIFEST.json',MANIFEST_SHA);truth=e.read_json(inputs/'TRUTH-FIXTURES.json',manifest['truth_sha256']);results=[]
    for entry in manifest['controls']:
        folder=BASE/'controls'/entry['name']
        if not folder.exists():
            results.append({'name':entry['name'],'execution_status':'NOT_EXECUTED_AFTER_REPLAY_STOP','reason':'frozen_batch_stopped_after_equal_replay_budget','whole_union_width_target_met':False});continue
        terminal=receipt(folder/'TERMINAL.json');inventory(folder,terminal)
        if not terminal['source_and_input_pins_stable'] or not terminal['checker_output_available'] or terminal['request_sha256']!=entry['sha256']:raise ValueError('unverified terminal evidence')
        request=e.read_request(folder/'REQUEST.json',entry['sha256']);result=e.read_json(folder/'checker.stdout',terminal['inventory']['checker.stdout']['sha256']);worker=e.read_json(folder/'producer.stdout',terminal['inventory']['producer.stdout']['sha256'])
        if result['ranked_histories'] is not None or result['recommended_history'] is not None or result['parameter_accuracy_released'] or result['statistical_coverage_verified']:raise ValueError('unsupported reliability release')
        counts={name:0 for name in entry['truth_ids']};unresolved=[];snapshots=0;stages={};inflight=0;unsupported=[]
        for path in sorted((folder/'journal').glob('state-*.json')):
            frame=e.read_json(path,terminal['inventory'][str(path.relative_to(folder))]['sha256']);snapshots+=1;transition=frame['transition']
            if transition['kind']=='started':inflight+=1
            if transition['kind']=='applied':
                key=transition['operator'];stages[key]=stages.get(key,0)+1
            if transition['kind']=='unsupported':unsupported.append(transition['detail'])
            for name in entry['truth_ids']:
                status=truth_status(frame['frontier'],truth['physical'][name],truth['verified_raw_moments_128'][name])
                if status=='CERTIFIED_AUGMENTED_CONTAINMENT':counts[name]+=1
                else:unresolved.append({'commit':path.name,'source':name,'status':status})
        final_truth={name:truth_status(result['augmented_states'],truth['physical'][name],truth['verified_raw_moments_128'][name]) for name in entry['truth_ids']}
        cover=result['physical_cover'];widths={};bounds={}
        for key in ops.PHYSICAL:
            original=request['physical'][key].width;tolerance=original*request['targets'][key]
            if cover:
                lo=min(F(cell['box'][key][0]) for cell in cover);hi=max(F(cell['box'][key][1]) for cell in cover);width=hi-lo;bounds[key]=[str(lo),str(hi)]
            else:width=None
            widths[key]={'original':str(original),'tolerance':str(tolerance),'width':None if width is None else str(width),'normalized_ratio':None if width is None or original==0 else str(width/original),'pre_fixed':original==0,'met':width is not None and width<=tolerance}
        met=bool(cover) and all(value['met'] for value in widths.values())
        if widths!=result['widths'] or met!=result['whole_union_width_target_met']:raise ValueError('whole-union target calculation mismatch')
        if entry['name']=='two_sources' and met:raise ValueError('impossible shared-source width target reported as met')
        unchanged=None
        if entry['name'] in ('uninformative','zero_budget'):
            unchanged=len(cover)==1 and cover[0]['box']=={key:[str(value.lo),str(value.hi)] for key,value in request['physical'].items()}
            if not unchanged:raise ValueError('required unchanged original root missing')
        results.append({'name':entry['name'],'status':result['status'],'mode':result['mode'],'stop_reason':worker['stop_reason'],'original_domain_preserved':True,'retained_states':len(cover),'whole_union_width_target_met':met,'widths':widths,'physical_union_bounds':bounds if cover else None,'producer_journal_readout_scope':'original_separate_checker_completed_numeric_replay_independent_replay_incomplete' if result['mode']=='normal_validated' else 'authenticated_producer_snapshots_only_not_a_derived_cover_certificate','independent_review_scope':'complete_inventory_and_ancestry_authentication_only', 'independent_numeric_replay':'same_cap_exhausted_original_domain_fallback' if entry['name']=='distinct' else 'not_retried_after_original_checker_cap', 'independently_reproduced_narrowed_cover':False, 'journal_snapshots':snapshots,'certified_augmented_containment_counts':counts,'unresolved_containment_checks':unresolved,'final_truth_checks':final_truth,'applied_stage_counts':stages,'stages_started_in_journal':inflight,'unsupported_stages':unsupported,'unchanged_original_root_check':unchanged,'validated_chain':result['details'],'terminal_sha256':e.sha((folder/'TERMINAL.json').read_bytes()),'checker_output_sha256':terminal['inventory']['checker.stdout']['sha256']})
    return {'schema':'original-domain-global-triangular-partial-batch-v1','batch_stopped_after':'equal','automatic_retry':False,'budgets_changed':False,'controls':results,'normalized_goal_all_coordinates':'1/20','two_source_normalized_h_separation':'1/6','smaller_supplied_domains':False,'statistical_coverage_claimed':False,'parameter_accuracy_released':False,'source_feasibility_claimed':False,'ranked_histories':None,'new_biological_data_or_simulation':False,'source_manifest_sha256':e.sha((BASE/'SOURCE-PINS.json').read_bytes()),'request_manifest_sha256':MANIFEST_SHA}
if __name__=='__main__':print(json.dumps(summarize(),sort_keys=True,indent=2))
