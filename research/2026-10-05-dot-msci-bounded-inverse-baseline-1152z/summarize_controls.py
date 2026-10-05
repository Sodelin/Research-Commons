"""Read-only control acceptance checks; no filtering, biological fitting or inference."""
import json
from decimal import Decimal
from fractions import Fraction as F
from pathlib import Path
import filter_core as c
import fixture_requests as fixtures
BASE=Path(__file__).resolve().parent
CONTROL_SHA='82db9ab367e3e07634bae7a6fc6c61d212acd5ba63f0d33897de2b38532f281d'

def includes(box,point):return all(F(box[name][0])<=value<=F(box[name][1]) for name,value in zip(c.COORDS,point))
def summarize():
    controls,_=c.read_json(BASE/'DECLARED-CONTROLS.json',CONTROL_SHA);reports=[]
    for control in controls:
        folder=BASE/'controls'/control['name'];terminal_path=folder/'TERMINAL.json'
        if terminal_path.is_symlink() or terminal_path.stat().st_size>c.MAX_FILE_BYTES:raise ValueError('invalid terminal receipt')
        raw=terminal_path.read_bytes()
        if len(raw)>c.MAX_FILE_BYTES:raise ValueError('oversized terminal receipt')
        def reject_nonfinite(_):raise ValueError('nonfinite receipt number')
        terminal=json.loads(raw,object_pairs_hook=c.no_duplicates,parse_float=Decimal,parse_constant=reject_nonfinite)
        if not terminal['source_and_input_pins_stable'] or not terminal['checker_output_available']:raise ValueError('terminal did not admit checker output')
        for name,item in terminal['inventory'].items():
            p=folder/name
            if p.is_symlink() or p.stat().st_size!=item['bytes'] or c.sha(p.read_bytes())!=item['sha256']:raise ValueError('terminal inventory changed')
        if terminal['request_sha256']!=control['sha256']:raise ValueError('request identity changed')
        result,_=c.read_json(folder/'checker.stdout',terminal['inventory']['checker.stdout']['sha256'])
        if result['ranked_histories'] is not None or result['recommended_history'] is not None or result['parameter_accuracy_released'] or result['statistical_coverage_verified']:raise ValueError('unsupported release claim')
        request=c.read_request(folder/'REQUEST.json',control['sha256']);truth_checks=None
        if control['name'] in {'distinct-contains','equal-contains','zero-budget'}:
            ref=fixtures.reference(request.provenance['fixture']);p={k:F(v) for k,v in ref['parameters'].items()};point=(p['h'],p['t1']-p['h'],p['t0']-p['t1'],p['rA'],p['rB'],p['rC'],p['rAB'],p['rR'],p['g'])
            truth_checks=0
            for path in sorted((folder/'checkpoints').glob('state-*.json')):
                state,_=c.read_json(path,terminal['inventory'][str(path.relative_to(folder))]['sha256'])
                if not any(includes(cell['box'],point) for cell in state['frontier']):raise ValueError('known generating point lost')
                truth_checks+=1
            if not any(includes(cell['box'],point) for cell in result['retained_cover']):raise ValueError('known generating point absent from final cover')
        if control['name'] in {'zero-budget','unsupported','broad'}:
            if len(result['retained_cover'])!=1 or result['retained_cover'][0]['box']!=c.box_record(request.box):raise ValueError('required full root retention failed')
        if control['name']=='broad' and c.radius(request.box)!=F(209,40):raise ValueError('broad radius mismatch')
        if control['name']=='separated' and result['status']!='EMPTY_COMPATIBLE_SET':raise ValueError('declared exclusion control inconclusive')
        reports.append({'name':control['name'],'status':result['status'],'retained_cells':len(result['retained_cover']),'request_sha256':control['sha256'],'terminal_sha256':c.sha((folder/'TERMINAL.json').read_bytes()),'checker_output_sha256':terminal['inventory']['checker.stdout']['sha256'],'checkpoints_preserving_generating_point':truth_checks,'root_radius':str(c.radius(request.box)),'cell_mesh_sup_width':result['cell_mesh_sup_width'],'union_sup_diameter':result['union_sup_diameter'],'details':result['details']})
    return {'schema':'bounded-inverse-arithmetic-controls-v1','controls':reports,'statistical_coverage_claimed':False,'parameter_accuracy_released':False,'ranked_histories':None,'new_biological_data':False,'scope':'Six bounded arithmetic controls only; broad-box radius209/40 prevents initial exclusion.'}

if __name__=='__main__':print(json.dumps(summarize(),sort_keys=True,indent=2))
