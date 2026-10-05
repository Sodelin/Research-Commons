"""Complete ancestry plus numerical replay; no inherited narrowing from partial chains."""
import re,time
from pathlib import Path
import global_engine as e
import global_contractors as ops
import interval_math as m
class InvalidCertificate(ValueError):pass
class ReplayBudget(ValueError):pass
PATTERN=re.compile(r'state-(\d{6})-([0-9a-f]{64})\.json')
KEYS={'schema','request_sha256','sources','contracts','forward_sha256','baseline_sha256','sequence','parent','transition','frontier'}

def header(path,request,sources):
    match=PATTERN.fullmatch(path.name)
    if match is None:raise InvalidCertificate('unsafe journal name')
    frame=e.read_json(path,match[2])
    if not isinstance(frame,dict) or set(frame)!=KEYS or frame['schema']!='global-triangular-commit-v1':raise InvalidCertificate('journal schema')
    if type(frame['sequence']) is not int or frame['sequence']!=int(match[1]):raise InvalidCertificate('sequence/name mismatch')
    if frame['request_sha256']!=request['identity'] or frame['sources']!=sources or frame['contracts']!=e.CONTRACTS or frame['forward_sha256']!=m.SOURCE_SHA or frame['baseline_sha256']!=e.BASELINE_SHA:raise InvalidCertificate('fixed provenance identity')
    return frame,match[2]

def ancestry(folder,request,sources,deadline,clock):
    folder=Path(folder)
    if folder.is_symlink():raise InvalidCertificate('journal directory symlink')
    budget=request['budget'];cap=2*budget['max_stages']+budget['max_splits']+budget['max_states']+1
    files=sorted(folder.glob('state-*.json'))
    if not files or len(files)>cap:raise InvalidCertificate('journal file count')
    current=files[-1];seen=set();chain=[];total=0;expected_sequence=None
    while True:
        if clock()>deadline:raise ReplayBudget('ancestry wall cap')
        if current.name in seen or len(chain)>=cap:raise InvalidCertificate('cycle/ancestry count')
        seen.add(current.name);total+=current.stat().st_size
        if total>e.MAX_JOURNAL_BYTES:raise ReplayBudget('ancestry total byte cap')
        frame,digest=header(current,request,sources);sequence=frame['sequence']
        if expected_sequence is not None and sequence!=expected_sequence:raise InvalidCertificate('nonconsecutive ancestry')
        chain.append((current,digest,sequence));parent=frame['parent']
        if sequence==0:
            if parent is not None:raise InvalidCertificate('genesis has a parent')
            break
        if not isinstance(parent,dict) or set(parent)!={'name','sha256'}:raise InvalidCertificate('missing parent identity')
        pm=PATTERN.fullmatch(parent['name']) if isinstance(parent.get('name'),str) else None
        if pm is None or pm[2]!=parent['sha256'] or int(pm[1])!=sequence-1:raise InvalidCertificate('unsafe/nonconsecutive parent')
        current=folder/parent['name'];expected_sequence=sequence-1
    chain.reverse()
    if len(chain)!=chain[-1][2]+1:raise InvalidCertificate('incomplete path to genesis')
    return chain,total

def validate(folder,request,sources,deadline,max_stages,clock=time.monotonic):
    if sources!=e.source_pins():raise InvalidCertificate('current source mismatch')
    chain,total=ancestry(folder,request,sources,deadline,clock);budget=request['budget'];active=None;started=0;recomputed=0;splits=0;excluded=0
    try:frontier={'r':e.initial_cell(request)};genesis={'kind':'genesis'}
    except m.Inconsistent:frontier={};genesis={'kind':'genesis_inconsistent'}
    previous=None
    for path,digest,sequence in chain:
        if clock()>deadline:raise ReplayBudget('numerical replay wall cap')
        frame,current_digest=header(path,request,sources)
        if current_digest!=digest or frame['parent']!=previous:raise InvalidCertificate('ancestry changed during replay')
        transition=frame['transition']
        if sequence==0:
            if transition!=genesis:raise InvalidCertificate('original genesis mismatch')
        else:
            if not isinstance(transition,dict) or transition.get('cell') not in frontier:raise InvalidCertificate('transition frontier identity')
            key=transition['cell'];cell=frontier[key];kind=transition.get('kind');plan=e.schedule(cell)
            if kind=='started':
                if active is not None or cell['status']!='pending' or cell['stage_index']>=len(plan):raise InvalidCertificate('invalid stage start')
                expected={'kind':'started','cell':key,'operator':plan[cell['stage_index']],'pre_state_sha256':e.state_hash(cell['state'])}
                if transition!=expected:raise InvalidCertificate('stage start identity')
                started+=1
                if started>budget['max_stages']:raise InvalidCertificate('stage count cap')
                frontier[key]={**cell,'status':'inflight'};active=key
            elif kind in ('applied','excluded','unsupported'):
                if active!=key or cell['status']!='inflight' or cell['stage_index']>=len(plan):raise InvalidCertificate('stage without retained pre-state')
                if recomputed>=max_stages:raise ReplayBudget('numerical replay count cap')
                operator=plan[cell['stage_index']];pre=e.state_hash(cell['state']);recomputed+=1
                try:post,detail=ops.operate(e.owned_state_copy(cell['state']),operator,budget['scalar_steps']);outcome='applied'
                except (m.Unsupported,m.forward.ResourceBound,m.forward.DomainError) as error:post=None;detail={'error_type':type(error).__name__,'reason':str(error)};outcome='unsupported'
                except m.Inconsistent as error:post=None;detail={'reason':str(error),'stage_detail':getattr(error,'stage_detail',None),'operator_detail':getattr(error,'operator_detail',None)};outcome='excluded'
                expected={'kind':outcome,'cell':key,'operator':operator,'pre_state_sha256':pre,'detail':detail}
                if transition!=expected:raise InvalidCertificate('numerical stage witness mismatch')
                if outcome=='applied':frontier[key]={**cell,'state':post,'stage_index':cell['stage_index']+1,'status':'pending'}
                elif outcome=='unsupported':frontier[key]={**cell,'status':'unsupported'}
                else:del frontier[key];excluded+=1
                active=None
            elif kind=='split':
                if active is not None or cell['status']!='pending' or cell['stage_index']<len(plan) or set(transition)!={'kind','cell','group','axis','midpoint','children'}:raise InvalidCertificate('AB split transition')
                group=transition['group'];axis=transition['axis']
                if (group,axis) not in (('aux','A'),('physical','rAB')) or len(key)-1>=budget['max_depth'] or len(frontier)>=budget['max_states']:raise InvalidCertificate('AB split axis/depth/state cap')
                value=cell['state'][group][axis];mid=(value.lo+value.hi)/2
                if value.width<=0 or transition['midpoint']!=str(mid) or transition['children']!=[key+'0',key+'1']:raise InvalidCertificate('closed split identity')
                splits+=1
                if splits>budget['max_splits']:raise InvalidCertificate('split count cap')
                children=[]
                for suffix,interval in [('0',m.I(value.lo,mid)),('1',m.I(mid,value.hi))]:
                    state=ops.clone(cell['state']);state[group][axis]=interval;children.append({'id':key+suffix,'state':state,'status':'pending','stage_index':0,'root_prefix':False})
                del frontier[key];frontier.update({child['id']:child for child in children})
            elif kind=='finished':
                if active is not None or cell['status']!='pending' or cell['stage_index']<len(plan) or transition!={'kind':'finished','cell':key}:raise InvalidCertificate('finished transition')
                frontier[key]={**cell,'status':'AB_budget_or_depth_unresolved'}
            else:raise InvalidCertificate('unrecognized transition')
        if len(frontier)>budget['max_states'] or frame['frontier']!=[e.cell_record(frontier[key]) for key in sorted(frontier)]:raise InvalidCertificate('complete frontier mismatch')
        previous={'name':path.name,'sha256':digest}
    if clock()>deadline:raise ReplayBudget('final replay wall cap')
    return frontier,{'journal_frames':len(chain),'authenticated_journal_bytes':total,'stages_started':started,'stages_recomputed':recomputed,'splits':splits,'exclusions':excluded,'inflight_pre_state_retained':active is not None,'final_commit_sha256':chain[-1][1]}

def output(request,frontier,mode,details):
    met,widths=e.goal(request,frontier);nonempty=bool(frontier)
    status=('EMPTY_COMPATIBLE_SET' if not nonempty else ('CONDITIONAL_UNION_WIDTH_CERTIFIED' if met else 'UNKNOWN_OUTER_COVER')) if mode=='normal_validated' else 'RECOVERED_UNKNOWN'
    return {'schema':'global-triangular-outer-cover-v1','status':status,'mode':mode,'request_sha256':request['identity'],'model':e.MODEL,'raw_feature_order':list(ops.FEATURES),'physical_cover':[{'id':key,'box':ops.record(frontier[key]['state'])['physical']} for key in sorted(frontier)],'augmented_states':[e.cell_record(frontier[key]) for key in sorted(frontier)],'nonempty_cover':nonempty,'whole_union_width_target_met':met,'widths':widths,'width_certificate_is_conditional_geometry_only':True,'source_feasibility_certified':False,'statistical_coverage_verified':False,'parameter_accuracy_released':False,'ranked_histories':None,'recommended_history':None,'details':details}

def recover(request_path,expected_request_sha,folder,sources,normal=False,clock=time.monotonic):
    try:request=e.read_request(request_path,expected_request_sha)
    except (OSError,ValueError,TypeError,KeyError) as error:return {'schema':'global-triangular-outer-cover-v1','status':'EVIDENCE_INVALID','physical_cover':None,'whole_union_width_target_met':False,'ranked_histories':None,'recommended_history':None,'parameter_accuracy_released':False,'statistical_coverage_verified':False,'error_type':type(error).__name__}
    p=request['physical'];A=p['h']+p['u'];T=A+p['v'];L=p['u']+p['v'];root_state={'physical':dict(p),'aux':dict(A=A,T=T,L=L),'moments':{key:m.I(0,1) for key in ops.FEATURES}}
    root={'r':{'id':'r','state':root_state,'status':'unresolved_original_root','stage_index':0,'root_prefix':True}}
    try:
        if request['budget']['recovery_wall_ms']==0:raise ReplayBudget('zero replay wall budget')
        frontier,details=validate(folder,request,sources,clock()+request['budget']['recovery_wall_ms']/1000,request['budget']['recovery_max_stages'],clock)
        return output(request,frontier,'normal_validated' if normal else 'recovered_validated_complete_chain',details)
    except (OSError,ValueError,TypeError,KeyError,IndexError,ArithmeticError) as error:return output(request,root,'recovered_authenticated_original_domain',{'all_inherited_narrowing_discarded':True,'failure_type':type(error).__name__,'reason':str(error)})

if __name__=='__main__':
    import argparse,json
    parser=argparse.ArgumentParser();parser.add_argument('--request',required=True);parser.add_argument('--request-sha256',required=True);parser.add_argument('--checkpoints',required=True);parser.add_argument('--source-pins',required=True);parser.add_argument('--source-pins-sha256',required=True);parser.add_argument('--normal',action='store_true');a=parser.parse_args()
    pins=e.read_json(a.source_pins,a.source_pins_sha256);allowed=set(e.SOURCE_FILES)|{'global_check.py'}
    if set(pins)!=allowed:raise ValueError('checker source pin allowlist')
    for name,digest in pins.items():
        if e.sha((e.BASE/name).read_bytes())!=digest:raise ValueError('checker source pin mismatch')
    print(json.dumps(recover(a.request,a.request_sha256,a.checkpoints,{name:pins[name] for name in e.SOURCE_FILES},normal=a.normal),sort_keys=True,indent=2))
