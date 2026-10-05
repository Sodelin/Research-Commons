"""Transactional bounded augmented-state contractor; completed output needs replay."""
import hashlib,importlib.util,json,os,re,sys,time
from pathlib import Path
from fractions import Fraction as F
import joint_contractor as ops
import interval_math as m
BASE=Path(__file__).resolve().parent
BASELINE=BASE.parent/'msci-bounded-inverse-filter-20261005-1102z/filter_core.py'
BASELINE_SHA='369697ef998cdd75cf3475b11e82c04b617838393446656a95f14887d180d13f'
if hashlib.sha256(BASELINE.read_bytes()).hexdigest()!=BASELINE_SHA:raise ValueError('baseline admission source changed')
_spec=importlib.util.spec_from_file_location('_seq_baseline_admission',BASELINE);legacy=importlib.util.module_from_spec(_spec);sys.modules[_spec.name]=legacy;_spec.loader.exec_module(legacy)
CONTRACT_SHA='1b34f0fa8f168e7ecf4310b432b015d973c71bfd2e44a0bb66364ca709b2b4ea'
SCHEMA='joint-interval-target-request-v1';MODEL='fixed-six-copy-clock-jc-nine-v1'
SCHEDULE=('joint',)
def schedule(request):return ('joint_zero',) if request['budget']['preconditioner']=='zero' else SCHEDULE
sha=legacy.sha;canonical=legacy.canonical
MAX_JSON_BYTES=8*1024**2

def read_json(path,expected=None):
    path=Path(path)
    if path.is_symlink() or path.stat().st_size>MAX_JSON_BYTES:raise ValueError('symlink/oversized JSON')
    raw=path.read_bytes()
    if len(raw)>MAX_JSON_BYTES or (expected is not None and sha(raw)!=expected):raise ValueError('JSON size/identity mismatch')
    def reject(_):raise ValueError('floating/nonfinite numerical input')
    return json.loads(raw,object_pairs_hook=legacy.no_duplicates,parse_float=reject,parse_constant=reject)

def read_request(path,expected):
    if not re.fullmatch('[0-9a-f]{64}',expected):raise ValueError('external request identity required')
    raw=read_json(path,expected)
    if not isinstance(raw,dict) or set(raw)!={'schema','model','quantity','box','features','budget','provenance'} or raw['schema']!=SCHEMA or raw['model']!=MODEL or raw['quantity']!='shifted_bernoulli_character_mean':raise ValueError('request schema/model')
    box=legacy.parse_box(raw['box']);physical={key:m.I(*bounds) for key,bounds in zip(ops.PHYSICAL,box)}
    if not isinstance(raw['features'],dict) or set(raw['features'])!=set(m.FEATURES):raise ValueError('exact nine selected features required')
    observations={key:m.I(*legacy.bounds(raw['features'][key])) for key in m.FEATURES}
    if any(value.lo<0 or value.hi>1 for value in observations.values()):raise ValueError('observed shifted mean range')
    limits={'max_operations':16,'max_splits':2,'max_depth':2,'sweeps_per_cell':4,'wall_ms':30000,'recovery_wall_ms':30000,'recovery_max_operations':16}
    budget=raw['budget']
    if not isinstance(budget,dict) or set(budget)!=set(limits)|{'preconditioner'}:raise ValueError('exact budget key set')
    if budget['preconditioner'] not in ('auto','zero'):raise ValueError('preconditioner mode')
    for key,cap in limits.items():
        if type(budget[key]) is not int or not 0<=budget[key]<=cap:raise ValueError('budget outside finite cap')
    if budget['sweeps_per_cell']<1:raise ValueError('positive sweep count')
    if not isinstance(raw['provenance'],dict):raise ValueError('provenance mapping required')
    return dict(identity=expected,physical=physical,observations=observations,budget=dict(budget),provenance=raw['provenance'])

def initial(request):return ops.initial(request['physical'],request['observations'])
def state_hash(state):return sha(canonical(ops.record(state)))
def cell_record(cell):return {**cell,'state':ops.record(cell['state'])}
def root_cell(request):return {'id':'r','state':initial(request),'status':'pending','step':0}
def source_pins():return {name:sha((BASE/name).read_bytes()) for name in ('interval_math.py','base_contractors.py','interval_ad.py','joint_contractor.py','seq_engine.py')}
class Store:
    def __init__(self,path,request,hook=None):self.path=Path(path);self.path.mkdir(exist_ok=False);self.request=request;self.hook=hook;self.last=None
    def commit(self,events,frontier):
        payload={'schema':'joint-nine-checkpoint-v1','request_sha256':self.request['identity'],'sources':source_pins(),'forward_sha256':m.SOURCE_SHA,'baseline_sha256':BASELINE_SHA,'contract_sha256':CONTRACT_SHA,'sequence':len(events),'events':events,'frontier':[cell_record(frontier[key]) for key in sorted(frontier)]}
        raw=canonical(payload)
        if len(raw)>MAX_JSON_BYTES:raise m.Unsupported('checkpoint encoding budget')
        target=self.path/f'state-{len(events):05d}-{sha(raw)}.json';temp=Path(str(target)+'.tmp')
        with temp.open('xb') as out:out.write(raw);out.flush();os.fsync(out.fileno())
        if self.hook:self.hook('before_commit',payload)
        os.link(temp,target);temp.unlink();self.last=target
        if self.hook:self.hook('after_commit',payload)
        return target

def split_physical(cell):
    # Deterministic joint-block cover order; these are still nine-coordinate states.
    priority=('h','g','u','rAB','v','rC','rR','rA','rB');offset=(len(cell['id'])-1)%len(priority)
    key=next((priority[(offset+i)%len(priority)] for i in range(len(priority)) if cell['state']['physical'][priority[(offset+i)%len(priority)]].width>0),None)
    if key is None:return None
    old=cell['state']['physical'][key];trial=(old.lo+old.hi)/2;children=[]
    for suffix,bounds in [('0',m.I(old.lo,trial)),('1',m.I(trial,old.hi))]:
        state=ops.clone(cell['state']);state['physical'][key]=bounds;children.append({'id':cell['id']+suffix,'state':state,'status':'pending','step':0})
    return key,children

def run(request,path,clock=time.monotonic,hook=None,operator=ops.operate):
    store=Store(path,request,hook);events=[]
    try:frontier={'r':root_cell(request)}
    except m.Inconsistent:
        # Initial impossible model-range projection is represented for replay explicitly.
        frontier={};events=[{'kind':'initial_inconsistent'}];store.commit(events,frontier);return {'stop_reason':'initial_inconsistent','certificate_issued':False}
    store.commit(events,frontier);start=clock();count=0;splits=0;budget=request['budget'];reason='complete_finite_sweeps'
    while True:
        pending=sorted(key for key,cell in frontier.items() if cell['status']=='pending')
        if not pending:break
        if count>=budget['max_operations']:reason='operation_budget';break
        if (clock()-start)*1000>=budget['wall_ms']:reason='wall_budget';break
        key=pending[0];cell=frontier[key]
        if cell['step']>=len(SCHEDULE)*budget['sweeps_per_cell']:
            proposed=split_physical(cell) if splits<budget['max_splits'] and len(key)-1<budget['max_depth'] else None
            if proposed is None:
                frontier[key]={**cell,'status':'finite_sweeps_finished'};events.append({'kind':'finished','cell':key});store.commit(events,frontier);continue
            axis,children=proposed;del frontier[key];frontier.update({child['id']:child for child in children});splits+=1;events.append({'kind':'split','cell':key,'axis':axis,'children':[cell_record(child) for child in children]});store.commit(events,frontier);continue
        kind=schedule(request)[cell['step']%len(SCHEDULE)];pre=state_hash(cell['state']);frontier[key]={**cell,'status':'inflight'};events.append({'kind':'started','cell':key,'operator':kind,'pre_state_sha256':pre});store.commit(events,frontier);count+=1
        try:post,detail=operator(cell['state'],kind);outcome='applied'
        except (m.Unsupported,m.forward.ResourceBound,m.forward.DomainError) as error:post=None;detail={'error_type':type(error).__name__,'reason':str(error)};outcome='unsupported'
        except m.Inconsistent as error:post=None;detail={'reason':str(error),'operator_detail':getattr(error,'operator_detail',None)};outcome='excluded'
        if (clock()-start)*1000>=budget['wall_ms']:reason='wall_budget';break
        if outcome=='applied':frontier[key]={**cell,'state':post,'step':cell['step']+1,'status':'pending'}
        elif outcome=='unsupported':frontier[key]={**cell,'status':'unsupported'}
        else:del frontier[key]
        event={'kind':outcome,'cell':key,'operator':kind,'pre_state_sha256':pre,'detail':detail}
        if post is not None:event['post_state']=ops.record(post)
        events.append(event);store.commit(events,frontier)
    return {'stop_reason':reason,'operations_started':count,'splits':splits,'certificate_issued':False,'requires_independent_replay':True,'checkpoint':None if store.last is None else store.last.name}

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--request',required=True);p.add_argument('--request-sha256',required=True);p.add_argument('--checkpoints',required=True);a=p.parse_args();print(json.dumps(run(read_request(a.request,a.request_sha256),a.checkpoints),indent=2))
