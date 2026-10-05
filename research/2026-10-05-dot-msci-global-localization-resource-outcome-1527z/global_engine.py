"""Bounded original-domain controller with complete parent-linked commit frontiers."""
import hashlib,importlib.util,json,os,re,sys,time
from pathlib import Path
from fractions import Fraction as F
import global_contractors as ops
import interval_math as m
BASE=Path(__file__).resolve().parent
BASELINE=BASE.parent/'msci-bounded-inverse-filter-20261005-1102z/filter_core.py'
BASELINE_SHA='369697ef998cdd75cf3475b11e82c04b617838393446656a95f14887d180d13f'
if hashlib.sha256(BASELINE.read_bytes()).hexdigest()!=BASELINE_SHA:raise ValueError('baseline parser changed')
spec=importlib.util.spec_from_file_location('_global_baseline',BASELINE);legacy=importlib.util.module_from_spec(spec);sys.modules[spec.name]=legacy;spec.loader.exec_module(legacy)
sha=legacy.sha;canonical=legacy.canonical
CONTRACTS={'global':'eb3120a1794413a608693255eba5b718df61140ad579049b24a77d29392ea940','AB_corners':'b7fe402f9bb4d53dbdf3881625a7e4e6cccba6a1013e94f5a53eb8f8c90a9dc5'}
SCHEMA='global-triangular-request-v1';MODEL='fixed-six-copy-clock-jc-nine-v1'
PREFIX=('root','linear','C','pulse','linear')
AB_SCHEDULE=('linear','AB','rates','forward','joint','linear')
MAX_JSON_BYTES=8*1024**2;MAX_JOURNAL_BYTES=256*1024**2
SOURCE_FILES=('interval_math.py','base_contractors.py','interval_ad.py','joint_contractor.py','global_contractors.py','global_engine.py')
def source_pins():return {name:sha((BASE/name).read_bytes()) for name in SOURCE_FILES}
def read_json(path,expected=None):
    p=Path(path)
    if p.is_symlink() or p.stat().st_size>MAX_JSON_BYTES:raise ValueError('JSON size/link')
    raw=p.read_bytes()
    if len(raw)>MAX_JSON_BYTES or expected is not None and sha(raw)!=expected:raise ValueError('JSON identity/size')
    def reject(_):raise ValueError('nonexact JSON number')
    return json.loads(raw,object_pairs_hook=legacy.no_duplicates,parse_float=reject,parse_constant=reject)

def read_request(path,expected):
    if not re.fullmatch('[0-9a-f]{64}',expected):raise ValueError('external request identity required')
    d=read_json(path,expected);keys={'schema','model','quantity','box','features','normalized_width_targets','budget','provenance'}
    if not isinstance(d,dict) or set(d)!=keys or d['schema']!=SCHEMA or d['model']!=MODEL or d['quantity']!='shifted_bernoulli_character_mean':raise ValueError('request schema/model')
    box=legacy.parse_box(d['box']);physical={key:m.I(*bounds) for key,bounds in zip(ops.PHYSICAL,box)}
    if not isinstance(d['features'],dict) or set(d['features'])!=set(ops.FEATURES):raise ValueError('nine feature schema')
    observed={key:m.I(*legacy.bounds(d['features'][key])) for key in ops.FEATURES}
    if any(value.lo<0 or value.hi>1 for value in observed.values()):raise ValueError('shifted feature range')
    if not isinstance(d['normalized_width_targets'],dict) or set(d['normalized_width_targets'])!=set(ops.PHYSICAL):raise ValueError('all-coordinate target vector')
    targets={key:legacy.rational(value) for key,value in d['normalized_width_targets'].items()}
    if any(value<=0 for value in targets.values()):raise ValueError('strictly positive width targets')
    caps={'scalar_steps':32,'max_stages':1024,'max_splits':63,'max_states':64,'max_depth':16,'wall_ms':120000,'recovery_wall_ms':120000,'recovery_max_stages':1024}
    budget=d['budget']
    if not isinstance(budget,dict) or set(budget)!=set(caps):raise ValueError('budget keys')
    for key,cap in caps.items():
        if type(budget[key]) is not int or not 0<=budget[key]<=cap:raise ValueError('finite budget exceeded')
    if budget['max_states']<1:raise ValueError('root needs one state')
    if not isinstance(d['provenance'],dict):raise ValueError('provenance mapping')
    return {'identity':expected,'physical':physical,'observed':observed,'targets':targets,'budget':dict(budget),'provenance':d['provenance']}

def schedule(cell):return (PREFIX if cell['root_prefix'] else ())+AB_SCHEDULE
def initial_cell(request):return {'id':'r','state':ops.initial(request['physical'],request['observed']),'status':'pending','stage_index':0,'root_prefix':True}
def state_hash(state):return sha(canonical(ops.record(state)))
def owned_state_copy(state):return {group:{key:m.I(value.lo,value.hi) for key,value in values.items()} for group,values in state.items()}
def cell_record(cell):return {**cell,'state':ops.record(cell['state'])}
def uninformed(request):return all(value.lo<=F(1,2) and value.hi>=1 for value in request['observed'].values())
def goal(request,frontier):
    boxes=[cell['state']['physical'] for cell in frontier.values()];widths={}
    for key in ops.PHYSICAL:
        old=request['physical'][key].width;target=old*request['targets'][key]
        width=max(box[key].hi for box in boxes)-min(box[key].lo for box in boxes) if boxes else None
        widths[key]={'original':str(old),'tolerance':str(target),'width':None if width is None else str(width),'normalized_ratio':None if width is None or old==0 else str(width/old),'pre_fixed':old==0,'met':width is not None and width<=target}
    return bool(boxes) and all(item['met'] for item in widths.values()),widths

class Store:
    def __init__(self,path,request,hook=None):
        self.path=Path(path);self.path.mkdir(exist_ok=False);self.request=request;self.hook=hook;self.last=None;self.last_sha=None;self.sequence=-1;self.sources=source_pins()
    def commit(self,transition,frontier):
        sequence=self.sequence+1;parent=None if self.last is None else {'name':self.last.name,'sha256':self.last_sha}
        data={'schema':'global-triangular-commit-v1','request_sha256':self.request['identity'],'sources':self.sources,'contracts':CONTRACTS,'forward_sha256':m.SOURCE_SHA,'baseline_sha256':BASELINE_SHA,'sequence':sequence,'parent':parent,'transition':transition,'frontier':[cell_record(frontier[key]) for key in sorted(frontier)]}
        raw=canonical(data)
        if len(raw)>MAX_JSON_BYTES:raise m.Unsupported('commit JSON cap')
        digest=sha(raw);target=self.path/f'state-{sequence:06d}-{digest}.json';tmp=Path(str(target)+'.tmp')
        with tmp.open('xb') as out:out.write(raw);out.flush();os.fsync(out.fileno())
        if self.hook:self.hook('before_commit',data)
        os.link(tmp,target);tmp.unlink();self.last=target;self.last_sha=digest;self.sequence=sequence
        if self.hook:self.hook('after_commit',data)
        return target

def split_AB(cell):
    # Alternate the two jointly unresolved AB coordinates, never select a source.
    choices=(('aux','A'),('physical','rAB')) if (len(cell['id'])-1)%2==0 else (('physical','rAB'),('aux','A'))
    chosen=next(((group,key) for group,key in choices if cell['state'][group][key].width>0),None)
    if chosen is None:return None
    group,key=chosen;old=cell['state'][group][key];mid=(old.lo+old.hi)/2;children=[]
    for suffix,interval in [('0',m.I(old.lo,mid)),('1',m.I(mid,old.hi))]:
        state=ops.clone(cell['state']);state[group][key]=interval;children.append({'id':cell['id']+suffix,'state':state,'status':'pending','stage_index':0,'root_prefix':False})
    return group,key,mid,children

def run(request,path,clock=time.monotonic,hook=None,operator=ops.operate):
    store=Store(path,request,hook);budget=request['budget'];start=clock();stages=0;splits=0
    try:frontier={'r':initial_cell(request)};genesis={'kind':'genesis'}
    except m.Inconsistent:frontier={};genesis={'kind':'genesis_inconsistent'}
    store.commit(genesis,frontier);reason='no_pending_states'
    while frontier:
        met,_=goal(request,frontier)
        if met:reason='whole_union_width_target_met';break
        if uninformed(request):reason='uninformative_model_range';break
        if (clock()-start)*1000>=budget['wall_ms']:reason='wall_budget';break
        pending=sorted(key for key,cell in frontier.items() if cell['status']=='pending')
        if not pending:break
        if stages>=budget['max_stages']:reason='stage_budget';break
        key=pending[0];cell=frontier[key];plan=schedule(cell)
        if cell['stage_index']>=len(plan):
            proposal=split_AB(cell) if splits<budget['max_splits'] and len(frontier)<budget['max_states'] and len(key)-1<budget['max_depth'] else None
            if proposal is None:
                frontier[key]={**cell,'status':'AB_budget_or_depth_unresolved'};store.commit({'kind':'finished','cell':key},frontier);continue
            group,axis,mid,children=proposal;del frontier[key];frontier.update({child['id']:child for child in children});splits+=1
            store.commit({'kind':'split','cell':key,'group':group,'axis':axis,'midpoint':str(mid),'children':[child['id'] for child in children]},frontier);continue
        kind=plan[cell['stage_index']];pre=state_hash(cell['state']);frontier[key]={**cell,'status':'inflight'}
        store.commit({'kind':'started','cell':key,'operator':kind,'pre_state_sha256':pre},frontier);stages+=1
        try:post,detail=operator(owned_state_copy(cell['state']),kind,budget['scalar_steps']);outcome='applied'
        except (m.Unsupported,m.forward.ResourceBound,m.forward.DomainError) as error:post=None;detail={'error_type':type(error).__name__,'reason':str(error)};outcome='unsupported'
        except m.Inconsistent as error:post=None;detail={'reason':str(error),'stage_detail':getattr(error,'stage_detail',None),'operator_detail':getattr(error,'operator_detail',None)};outcome='excluded'
        if (clock()-start)*1000>=budget['wall_ms']:reason='wall_budget';break
        if outcome=='applied':frontier[key]={**cell,'state':post,'stage_index':cell['stage_index']+1,'status':'pending'}
        elif outcome=='unsupported':frontier[key]={**cell,'status':'unsupported'}
        else:del frontier[key]
        store.commit({'kind':outcome,'cell':key,'operator':kind,'pre_state_sha256':pre,'detail':detail},frontier)
    met,widths=goal(request,frontier)
    return {'schema':'global-triangular-worker-outcome-v1','stop_reason':reason if frontier else 'empty_compatible_cover','stages_started':stages,'splits':splits,'whole_union_width_goal_observed':met,'widths':widths,'certificate_issued':False,'requires_independent_complete_chain_replay':True,'checkpoint':None if store.last is None else store.last.name}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--request',required=True);p.add_argument('--request-sha256',required=True);p.add_argument('--checkpoints',required=True);a=p.parse_args();print(json.dumps(run(read_request(a.request,a.request_sha256),a.checkpoints),sort_keys=True,indent=2))
