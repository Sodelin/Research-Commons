"""Independent transition replay and full physical-union export; no feasibility claim."""
import re,time
from pathlib import Path
import seq_engine as e
import joint_contractor as ops
import interval_math as m
class InvalidCertificate(ValueError):pass
class ReplayBudget(ValueError):pass

def valid_checkpoint(path,request,expected_sources,deadline,max_operations,clock=time.monotonic):
    path=Path(path);match=re.fullmatch(r'state-(\d{5})-([0-9a-f]{64})\.json',path.name)
    if match is None:raise InvalidCertificate('checkpoint name')
    data=e.read_json(path,match[2]);keys={'schema','request_sha256','sources','forward_sha256','baseline_sha256','contract_sha256','sequence','events','frontier'}
    if not isinstance(data,dict) or set(data)!=keys or data['schema']!='joint-nine-checkpoint-v1':raise InvalidCertificate('checkpoint schema')
    if data['request_sha256']!=request['identity'] or data['sources']!=expected_sources or expected_sources!=e.source_pins() or data['forward_sha256']!=m.SOURCE_SHA or data['baseline_sha256']!=e.BASELINE_SHA or data['contract_sha256']!=e.CONTRACT_SHA:raise InvalidCertificate('source/input/contract identity')
    events=data['events'];budget=request['budget']
    if not isinstance(events,list) or type(data['sequence']) is not int or data['sequence']!=len(events) or int(match[1])!=len(events) or len(events)>2*budget['max_operations']+3*budget['max_splits']+3:raise InvalidCertificate('event count')
    try:frontier={'r':e.root_cell(request)};initial_empty=False
    except m.Inconsistent:frontier={};initial_empty=True
    if initial_empty:
        if events!=[{'kind':'initial_inconsistent'}] or data['frontier']!=[]:raise InvalidCertificate('initial inconsistency proof')
        return frontier,{'operations_recomputed':0,'exclusions':1,'splits':0,'checkpoint_sha256':match[2]}
    active=None;count=0;recomputed=0;splits=0;exclusions=0
    for event in events:
        if clock()>deadline:raise ReplayBudget('replay wall budget')
        if not isinstance(event,dict) or event.get('cell') not in frontier:raise InvalidCertificate('event frontier identity')
        key=event['cell'];cell=frontier[key];kind=event.get('kind')
        if kind=='started':
            expected={'kind':'started','cell':key,'operator':e.schedule(request)[cell['step']%len(e.SCHEDULE)],'pre_state_sha256':e.state_hash(cell['state'])}
            if active is not None or cell['status']!='pending' or cell['step']>=len(e.SCHEDULE)*budget['sweeps_per_cell'] or event!=expected:raise InvalidCertificate('start transition')
            count+=1
            if count>budget['max_operations']:raise InvalidCertificate('operation count limit')
            frontier[key]={**cell,'status':'inflight'};active=key
        elif kind in ('applied','excluded','unsupported'):
            operator=e.schedule(request)[cell['step']%len(e.SCHEDULE)];pre=e.state_hash(cell['state'])
            if active!=key or cell['status']!='inflight' or event.get('operator')!=operator or event.get('pre_state_sha256')!=pre:raise InvalidCertificate('operator pre-state')
            if recomputed>=max_operations:raise ReplayBudget('operation replay cap')
            recomputed+=1
            try:post,detail=ops.operate(cell['state'],operator);expected_kind='applied'
            except (m.Unsupported,m.forward.ResourceBound,m.forward.DomainError) as error:post=None;detail={'error_type':type(error).__name__,'reason':str(error)};expected_kind='unsupported'
            except m.Inconsistent as error:post=None;detail={'reason':str(error),'operator_detail':getattr(error,'operator_detail',None)};expected_kind='excluded'
            expected={'kind':expected_kind,'cell':key,'operator':operator,'pre_state_sha256':pre,'detail':detail}
            if post is not None:expected['post_state']=ops.record(post)
            if event!=expected:raise InvalidCertificate('mathematical operator witness mismatch')
            if kind=='applied':frontier[key]={**cell,'state':post,'step':cell['step']+1,'status':'pending'}
            elif kind=='unsupported':frontier[key]={**cell,'status':'unsupported'}
            else:del frontier[key];exclusions+=1
            active=None
        elif kind=='split':
            if active is not None or cell['status']!='pending' or cell['step']<len(e.SCHEDULE)*budget['sweeps_per_cell'] or set(event)!={'kind','cell','axis','children'}:raise InvalidCertificate('split transition')
            axis=event['axis']
            if axis not in ops.PHYSICAL or len(key)-1>=budget['max_depth']:raise InvalidCertificate('physical-only split/depth')
            interval=cell['state']['physical'][axis]
            if interval.width<=0:raise InvalidCertificate('degenerate split')
            midpoint=(interval.lo+interval.hi)/2;children=[]
            for suffix,bounds in [('0',m.I(interval.lo,midpoint)),('1',m.I(midpoint,interval.hi))]:
                state=ops.clone(cell['state']);state['physical'][axis]=bounds;children.append({'id':key+suffix,'state':state,'step':0,'status':'pending'})
            if event['children']!=[e.cell_record(child) for child in children]:raise InvalidCertificate('both complete closed children required')
            splits+=1
            if splits>budget['max_splits']:raise InvalidCertificate('split count')
            del frontier[key];frontier.update({child['id']:child for child in children})
        elif kind=='finished':
            if active is not None or cell['status']!='pending' or cell['step']<len(e.SCHEDULE)*budget['sweeps_per_cell'] or event!={'kind':'finished','cell':key}:raise InvalidCertificate('finished transition')
            frontier[key]={**cell,'status':'finite_sweeps_finished'}
        else:raise InvalidCertificate('unrecognized transition')
    if clock()>deadline:raise ReplayBudget('replay wall budget')
    if data['frontier']!=[e.cell_record(frontier[key]) for key in sorted(frontier)]:raise InvalidCertificate('exported frontier mismatch')
    return frontier,{'operations_recomputed':recomputed,'exclusions':exclusions,'splits':splits,'inflight_pre_state_retained':active is not None,'checkpoint_sha256':match[2]}

def output(request,frontier,mode,details):
    cover=[{'id':key,'box':ops.record(frontier[key]['state'])['physical']} for key in sorted(frontier)]
    boxes=[cell['state']['physical'] for cell in frontier.values()]
    diameter=max((max(box[key].hi for box in boxes)-min(box[key].lo for box in boxes) for key in ops.PHYSICAL),default=None) if boxes else None
    mesh=max((interval.width for box in boxes for interval in box.values()),default=m.F(0))
    status=('EMPTY_COMPATIBLE_SET' if not boxes else 'UNKNOWN_OUTER_COVER') if mode=='normal_validated' else 'RECOVERED_UNKNOWN'
    return {'schema':'joint-interval-target-cover-v1','status':status,'mode':mode,'request_sha256':request['identity'],'physical_cover':cover,'augmented_states':[e.cell_record(frontier[key]) for key in sorted(frontier)],'export_is_enlargement_only':True,'physical_union_sup_diameter':None if diameter is None else str(diameter),'physical_cell_mesh':str(mesh),'statistical_coverage_verified':False,'parameter_accuracy_released':False,'ranked_histories':None,'recommended_history':None,'all_nine_coordinates':list(ops.PHYSICAL),'details':details}

def recover(request_path,expected_request_sha,folder,expected_sources,normal=False,clock=time.monotonic):
    try:request=e.read_request(request_path,expected_request_sha)
    except (OSError,ValueError,TypeError,KeyError) as error:return {'schema':'joint-interval-target-cover-v1','status':'EVIDENCE_INVALID','physical_cover':None,'ranked_histories':None,'recommended_history':None,'cover_certificate_issued':False,'parameter_accuracy_released':False,'statistical_coverage_verified':False,'error_type':type(error).__name__}
    # A conservative fallback deliberately discards all moment/auxiliary tightening.
    p=request['physical'];A=p['h']+p['u'];T=A+p['v'];L=p['u']+p['v'];state={'physical':dict(p),'aux':dict(A=A,T=T,L=L),'moments':{key:m.I(0,1) for key in m.FEATURES}}
    root={'r':{'id':'r','state':state,'status':'unresolved_original_root','step':0}}
    try:
        folder=Path(folder)
        if folder.is_symlink():raise InvalidCertificate('symlink checkpoint directory')
        files=sorted(folder.glob('state-*.json'));budget=request['budget']
        if not files or len(files)>2*budget['max_operations']+3*budget['max_splits']+4:raise InvalidCertificate('checkpoint count')
        if budget['recovery_wall_ms']==0:raise ReplayBudget('zero replay budget')
        frontier,details=valid_checkpoint(files[-1],request,expected_sources,clock()+budget['recovery_wall_ms']/1000,budget['recovery_max_operations'],clock)
        return output(request,frontier,'normal_validated' if normal else 'recovered_validated_checkpoint',details)
    except (OSError,ValueError,TypeError,KeyError,IndexError,ArithmeticError) as error:return output(request,root,'recovered_authenticated_root',{'all_inherited_contractions_discarded':True,'failure_type':type(error).__name__,'reason':str(error)})

if __name__=='__main__':
    import argparse,json
    parser=argparse.ArgumentParser();parser.add_argument('--request',required=True);parser.add_argument('--request-sha256',required=True);parser.add_argument('--checkpoints',required=True);parser.add_argument('--source-pins',required=True);parser.add_argument('--source-pins-sha256',required=True);parser.add_argument('--normal',action='store_true');a=parser.parse_args()
    pins=e.read_json(a.source_pins,a.source_pins_sha256)
    for name,digest in pins.items():
        if name not in ('interval_math.py','base_contractors.py','interval_ad.py','joint_contractor.py','seq_engine.py','seq_check.py') or e.sha((e.BASE/name).read_bytes())!=digest:raise ValueError('checker source pin mismatch')
    if set(pins)!=set(('interval_math.py','base_contractors.py','interval_ad.py','joint_contractor.py','seq_engine.py','seq_check.py')):raise ValueError('checker pin allowlist')
    expected={name:pins[name] for name in ('interval_math.py','base_contractors.py','interval_ad.py','joint_contractor.py','seq_engine.py')}
    print(json.dumps(recover(a.request,a.request_sha256,a.checkpoints,expected,normal=a.normal),sort_keys=True,indent=2))
