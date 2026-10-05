"""Independent checkpoint replay: geometry AND each numerical exclusion witness."""
import re,time
from fractions import Fraction as F
from pathlib import Path
import filter_core as c

class BadCertificate(ValueError):pass

def checked_witness(cell_id,box,w,request,provider,cache):
    # Recompute centre, time conversion and anisotropic radius, not stored values.
    centre=tuple((a+b)/2 for a,b in box)
    duration_radius=max((b-a)/2 for a,b in box[:3]);rate_radius=max((b-a)/2 for a,b in box[3:8]);gamma_radius=(box[8][1]-box[8][0])/2
    largest_duration=max(b for a,b in box[:3]);smallest_rate=min(a for a,b in box[3:8]);largest_rate=max(b for a,b in box[3:8])
    error=(3*largest_duration+F(1)/smallest_rate)*rate_radius+2*gamma_radius+12*largest_rate*duration_radius
    p={'h':centre[0],'t1':sum(centre[:2]),'t0':sum(centre[:3]),'rA':centre[3],'rB':centre[4],'rC':centre[5],'rAB':centre[6],'rR':centre[7],'g':centre[8]}
    if not isinstance(w,dict) or w.get('pair') not in c.PAIRS or type(w.get('k')) is not int or not 1<=w['k']<=55:raise BadCertificate('invalid witness coordinate')
    key=(centre,request.budget['precision_bits'])
    if key not in cache:cache[key]=provider.evaluate(p,request.budget['precision_bits'])[2]
    point=cache[key][w['pair']][w['k']-1];enclosed=(max(F(0),point.lo-error),min(F(1),point.hi+error))
    data=request.observations[c.PAIRS.index(w['pair'])*55+w['k']-1]
    if enclosed[1]<data[0]:side='below'
    elif enclosed[0]>data[1]:side='above'
    else:raise BadCertificate('no strict interval separation')
    expected={'cell':cell_id,'box':c.box_record(box),'centre':{name:str(v) for name,v in zip(c.COORDS,centre)},'absolute_parameters':{name:str(v) for name,v in p.items()},'radius':str(error),'forward_sha256':c.FORWARD_SHA,'precision_bits':request.budget['precision_bits'],'pair':w['pair'],'k':w['k'],'point_interval':[str(point.lo),str(point.hi)],'envelope':[str(x) for x in enclosed],'observation':[str(x) for x in data],'strict_side':side}
    if w!=expected:raise BadCertificate('witness arithmetic/query/identity mismatch')

def validate_checkpoint(path,request,expected_producer_sha,deadline,max_witnesses,clock=time.monotonic):
    path=Path(path);match=re.fullmatch(r'state-(\d{5})-([0-9a-f]{64})\.json',path.name)
    if not match:raise BadCertificate('invalid checkpoint name')
    payload,_=c.read_json(path,match[2])
    expected_keys={'schema','request_sha256','producer_sha256','forward_sha256','corollary_sha256','sequence','events','frontier'}
    if not isinstance(payload,dict) or set(payload)!=expected_keys or payload['schema']!='msci-filter-checkpoint-v1':raise BadCertificate('checkpoint schema')
    if payload['request_sha256']!=request.identity or payload['producer_sha256']!=expected_producer_sha or payload['forward_sha256']!=c.FORWARD_SHA or payload['corollary_sha256']!=c.COROLLARY_SHA:raise BadCertificate('checkpoint provenance mismatch')
    events=payload['events']
    if not isinstance(events,list) or len(events)>2*request.budget['max_evaluations'] or type(payload['sequence']) is not int or payload['sequence']!=len(events) or int(match[1])!=len(events):raise BadCertificate('event/sequence bounds')
    frontier={'r':(request.box,'pending')};evaluations=0;splits=0;excluded=0;inflight=None;provider=None;cache={}
    for event in events:
        if clock()>deadline:raise c.ValidationBudget('checkpoint validation wall budget')
        if not isinstance(event,dict) or event.get('cell') not in frontier:raise BadCertificate('event names missing frontier cell')
        cell=event['cell'];box,status=frontier[cell];kind=event.get('kind')
        if kind=='started':
            if set(event)!={'kind','cell'} or inflight is not None or status!='pending':raise BadCertificate('invalid start transition')
            evaluations+=1
            if evaluations>request.budget['max_evaluations']:raise BadCertificate('evaluation budget exceeded')
            frontier[cell]=(box,'inflight');inflight=cell
        elif kind=='split':
            if set(event)!={'kind','cell','axis','left','right'} or inflight!=cell or status!='inflight':raise BadCertificate('split without retained inflight parent')
            axis=event['axis']
            if type(axis) is not int or not 0<=axis<9 or event['left']!=cell+'0' or event['right']!=cell+'1' or len(cell)-1>=request.budget['max_depth']:raise BadCertificate('split identity/depth')
            a,b=box[axis]
            if a>=b:raise BadCertificate('zero width split')
            # Independently reconstruct both closed children from the parent.
            mid=(a+b)/2;left=list(box);right=list(box);left[axis]=(a,mid);right[axis]=(mid,b)
            del frontier[cell];frontier[cell+'0']=(tuple(left),'pending');frontier[cell+'1']=(tuple(right),'pending');inflight=None;splits+=1
            if splits>request.budget['max_splits']:raise BadCertificate('split budget exceeded')
        elif kind=='excluded':
            if set(event)!={'kind','cell','witness'} or inflight!=cell or status!='inflight':raise BadCertificate('exclusion without inflight parent')
            if excluded>=max_witnesses:raise c.ValidationBudget('witness validation count budget')
            if provider is None:provider=c.load_forward()
            checked_witness(cell,box,event['witness'],request,provider,cache)
            if clock()>deadline:raise c.ValidationBudget('witness validation wall budget')
            excluded+=1;del frontier[cell];inflight=None
        elif kind=='retained':
            reason=event.get('reason');allowed={'cell_mesh','depth_budget','split_budget','unsupported_evaluation'}
            keys={'kind','cell','reason'}|({'error_type'} if reason=='unsupported_evaluation' else set())
            if set(event)!=keys or reason not in allowed or inflight!=cell or status!='inflight':raise BadCertificate('invalid retained transition')
            if reason=='cell_mesh' and max(b-a for a,b in box)>request.budget['cell_mesh']:raise BadCertificate('false cell mesh flag')
            if reason=='depth_budget' and len(cell)-1<request.budget['max_depth']:raise BadCertificate('false depth budget flag')
            if reason=='split_budget' and splits<request.budget['max_splits']:raise BadCertificate('false split budget flag')
            frontier[cell]=(box,'unsupported' if reason=='unsupported_evaluation' else reason);inflight=None
        else:raise BadCertificate('unknown event kind')
    if clock()>deadline:raise c.ValidationBudget('checkpoint validation wall budget')
    actual=[{'id':key,'box':c.box_record(frontier[key][0]),'status':frontier[key][1]} for key in sorted(frontier)]
    if payload['frontier']!=actual:raise BadCertificate('missing/altered retained region')
    return actual,{'exclusion_witnesses_recomputed':excluded,'split_count':splits,'evaluations_started':evaluations,'inflight_cell_included':inflight is not None,'checkpoint_sha256':match[2]}

def result_record(request,frontier,mode,details):
    # These boxes were reconstructed from authenticated inputs, not untrusted strings.
    # Dyadic refinement may legitimately exceed the original input encoding cap.
    boxes=[tuple(tuple(F(v) for v in x['box'][key]) for key in c.COORDS) for x in frontier]
    mesh=max((b-a for box in boxes for a,b in box),default=F(0))
    diameter=max((max(box[i][1] for box in boxes)-min(box[i][0] for box in boxes) for i in range(9)),default=F(0)) if boxes else None
    status='RECOVERED_UNKNOWN' if mode!='normal_validated' else ('UNKNOWN_OUTER_COVER' if boxes else 'EMPTY_COMPATIBLE_SET')
    return {'schema':'bounded-msci-outer-cover-v1','status':status,'mode':mode,'request_sha256':request.identity,'model':c.MODEL,'quantity':c.QUANTITY,'all_nine_coordinates':list(c.COORDS),'retained_cover':frontier,'cell_mesh_sup_width':str(mesh),'all_cells_meet_requested_mesh':mesh<=request.budget['cell_mesh'],'union_sup_diameter':None if diameter is None else str(diameter),'diameter_is_only_geometric':True,'parameter_accuracy_released':False,'statistical_coverage_verified':False,'conditional_coverage':'Contains every x in the authenticated original box whose330 true feature means satisfy all supplied intervals. A probability guarantee requires separate source/data/interval admission.','ranked_histories':None,'recommended_history':None,'details':details}

def certify_or_recover(request_path,expected_request_sha,checkpoints,expected_producer_sha,normal=False,clock=time.monotonic):
    # Original identity comes from the caller, never from a checkpoint.
    try:request=c.read_request(request_path,expected_request_sha)
    except (OSError,ValueError,TypeError,KeyError) as error:
        return {'schema':'bounded-msci-outer-cover-v1','status':'EVIDENCE_INVALID','retained_cover':None,'cover_certificate_issued':False,'error_type':type(error).__name__,'ranked_histories':None,'recommended_history':None}
    root=[c.Cell('r',request.box,'unresolved_root_fallback').record()]
    details={'original_request_authenticated':True,'inherited_exclusions':False}
    try:
        folder=Path(checkpoints)
        if folder.is_symlink():raise BadCertificate('checkpoint directory symlink')
        files=sorted(folder.glob('state-*.json'))
        if not files or len(files)>1+2*request.budget['max_evaluations']:raise BadCertificate('missing/excessive checkpoints')
        if request.budget['recovery_wall_ms']==0:raise c.ValidationBudget('zero recovery budget')
        frontier,evidence=validate_checkpoint(files[-1],request,expected_producer_sha,clock()+request.budget['recovery_wall_ms']/1000,request.budget['recovery_max_witnesses'],clock)
        mode='normal_validated' if normal else 'recovered_validated_checkpoint'
        return result_record(request,frontier,mode,{**details,**evidence,'inherited_exclusions':evidence['exclusion_witnesses_recomputed']>0})
    except (OSError,ValueError,TypeError,KeyError,IndexError,ArithmeticError) as error:
        details.update(validation_failure=type(error).__name__,reason=str(error),checkpoint_exclusions_discarded=True)
        return result_record(request,root,'recovered_authenticated_root',details)

if __name__=='__main__':
    import argparse,json
    parser=argparse.ArgumentParser();parser.add_argument('--request',required=True);parser.add_argument('--request-sha256',required=True);parser.add_argument('--checkpoints',required=True);parser.add_argument('--producer-sha256',required=True);parser.add_argument('--normal',action='store_true');args=parser.parse_args()
    print(json.dumps(certify_or_recover(args.request,args.request_sha256,args.checkpoints,args.producer_sha256,normal=args.normal),sort_keys=True,indent=2))
