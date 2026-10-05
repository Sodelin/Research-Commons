"""Bounded SIVIA-style outer filtering; no posterior/uniqueness claim."""
import hashlib,importlib.util,json,os,re,sys,time
from dataclasses import dataclass,replace
from fractions import Fraction as F
from pathlib import Path
BASE=Path(__file__).resolve().parent
FORWARD_PATH=BASE.parent/'msci-330-feature-public-20261005-1039z/evaluator/certified_forward.py'
FORWARD_SHA='c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace'
COROLLARY_SHA='4ce2908f87a88584be18a49444c1c0ad06e07ec58d304130b565a18a8ff556ac'
COORDS=('h','u','v','rA','rB','rC','rAB','rR','g')
PAIRS=('AA','BB','CC','AB','BC','AC')
MODEL='fixed-six-copy-clock-jc-330-v1'
QUANTITY='shifted_bernoulli_character_mean'
MAX_FILE_BYTES=1048576
class Invalid(ValueError):pass
class ValidationBudget(ValueError):pass

def sha(data):return hashlib.sha256(data).hexdigest()
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode()
def no_duplicates(pairs):
    d={}
    for k,v in pairs:
        if k in d:raise Invalid('duplicate JSON key')
        d[k]=v
    return d

def read_json(path,expected=None):
    path=Path(path)
    if path.is_symlink() or path.stat().st_size>MAX_FILE_BYTES:raise Invalid('symlink/oversized file')
    with path.open('rb') as src:raw=src.read(MAX_FILE_BYTES+1)
    if len(raw)>MAX_FILE_BYTES:raise Invalid('oversized file after read')
    if expected is not None and sha(raw)!=expected:raise Invalid('expected file hash mismatch')
    def reject(_):raise Invalid('floating/nonfinite JSON number')
    return json.loads(raw,object_pairs_hook=no_duplicates,parse_float=reject,parse_constant=reject),sha(raw)

def rational(x):
    if isinstance(x,bool) or isinstance(x,float):raise Invalid('exact rational required')
    if isinstance(x,F):v=x
    elif isinstance(x,int):v=F(x)
    elif isinstance(x,str) and len(x)<=160 and re.fullmatch(r'-?\d+(?:/[1-9]\d*)?',x):v=F(x)
    else:raise Invalid('bounded rational input required')
    if max(abs(v.numerator).bit_length(),v.denominator.bit_length())>256:raise Invalid('reduced rational cap')
    return v

def bounds(x):
    if not isinstance(x,list) or len(x)!=2:raise Invalid('two endpoints required')
    a,b=map(rational,x)
    if a>b:raise Invalid('reversed interval')
    return a,b

def box_record(box):return {k:[str(a),str(b)] for k,(a,b) in zip(COORDS,box)}
def parse_box(d):
    if not isinstance(d,dict) or set(d)!=set(COORDS):raise Invalid('all nine coordinates required')
    b=tuple(bounds(d[k]) for k in COORDS)
    if any(a<=0 for a,z in b[:8]) or not 0<b[8][0]<=b[8][1]<1:raise Invalid('strict source margins required')
    return b

def load_forward():
    raw=FORWARD_PATH.read_bytes()
    if sha(raw)!=FORWARD_SHA:raise Invalid('published forward source changed')
    name='_published_msci_forward_c848';spec=importlib.util.spec_from_file_location(name,FORWARD_PATH);mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod;spec.loader.exec_module(mod);return mod

@dataclass(frozen=True)
class Request:
    identity:str
    box:tuple
    observations:tuple
    budget:dict
    provenance:dict


def read_request(path,expected):
    if not re.fullmatch('[0-9a-f]{64}',expected):raise Invalid('external request hash required')
    d,h=read_json(path,expected)
    required={'schema','model','quantity','box','features','budget','provenance'}
    if not isinstance(d,dict) or set(d)!=required or d['schema']!='bounded-msci-filter-request-v1' or d['model']!=MODEL or d['quantity']!=QUANTITY:raise Invalid('request schema/model/quantity')
    box=parse_box(d['box']);features=d['features'];obs=[]
    if not isinstance(features,dict) or set(features)!=set(PAIRS):raise Invalid('six feature pair labels required')
    for pair in PAIRS:
        rows=features[pair]
        if not isinstance(rows,list) or len(rows)!=55:raise Invalid('all55 feature indices required')
        for k,row in enumerate(rows,1):
            if not isinstance(row,dict) or set(row)!={'k','bounds'} or type(row['k']) is not int or row['k']!=k:raise Invalid('unique ordered k1..55 required')
            a,b=bounds(row['bounds'])
            if not 0<=a<=b<=1:raise Invalid('feature bounds outside[0,1]')
            obs.append((a,b))
    budget=d['budget'];caps={'max_evaluations':32,'max_splits':32,'max_depth':32,'wall_ms':30000,'recovery_wall_ms':30000,'recovery_max_witnesses':32}
    if not isinstance(budget,dict) or set(budget)!=set(caps)|{'precision_bits','cell_mesh'}:raise Invalid('budget fields')
    for key,cap in caps.items():
        if type(budget[key]) is not int or not 0<=budget[key]<=cap:raise Invalid('budget cap: '+key)
    if type(budget['precision_bits']) is not int or not 16<=budget['precision_bits']<=128:raise Invalid('precision cap')
    budget=dict(budget);budget['cell_mesh']=rational(budget['cell_mesh'])
    if budget['cell_mesh']<0:raise Invalid('negative mesh')
    if not isinstance(d['provenance'],dict):raise Invalid('provenance record required')
    return Request(h,box,tuple(obs),budget,d['provenance'])

@dataclass(frozen=True)
class Cell:
    identity:str
    box:tuple
    status:str='pending'
    def record(self):return {'id':self.identity,'box':box_record(self.box),'status':self.status}

def midpoint(box):return tuple((a+b)/2 for a,b in box)
def absolute_parameters(c):
    return dict(h=c[0],t1=c[0]+c[1],t0=c[0]+c[1]+c[2],rA=c[3],rB=c[4],rC=c[5],rAB=c[6],rR=c[7],g=c[8])
def radius(box):
    widths=[(b-a)/2 for a,b in box];b=max(z for a,z in box[:3]);rmin=min(a for a,z in box[3:8]);rmax=max(z for a,z in box[3:8])
    return (3*b+1/rmin)*max(widths[3:8])+2*widths[8]+12*rmax*max(widths[:3])
def interval_record(x):return [str(x[0]),str(x[1])]
def envelope(interval,error):return max(F(0),interval.lo-error),min(F(1),interval.hi+error)
def disjoint(a,b):return a[1]<b[0] or a[0]>b[1]
def split_cell(cell,axis):
    a,b=cell.box[axis]
    if a==b:raise Invalid('cannot split zero-width axis')
    m=(a+b)/2;left=list(cell.box);right=list(cell.box);left[axis]=(a,m);right[axis]=(m,b)
    return Cell(cell.identity+'0',tuple(left)),Cell(cell.identity+'1',tuple(right))

def witness_for(cell,request,provider):
    c=midpoint(cell.box);p=absolute_parameters(c);error=radius(cell.box)
    _,_,means=provider.evaluate(p,request.budget['precision_bits'])
    for index,(pair,k) in enumerate((pair,k) for pair in PAIRS for k in range(1,56)):
        value=means[pair][k-1];e=envelope(value,error);observed=request.observations[index]
        if disjoint(e,observed):
            return {'cell':cell.identity,'box':box_record(cell.box),'centre':{key:str(v) for key,v in zip(COORDS,c)},'absolute_parameters':{key:str(v) for key,v in p.items()},'radius':str(error),'forward_sha256':FORWARD_SHA,'precision_bits':request.budget['precision_bits'],'pair':pair,'k':k,'point_interval':[str(value.lo),str(value.hi)],'envelope':interval_record(e),'observation':interval_record(observed),'strict_side':'below' if e[1]<observed[0] else 'above'}
    return None

class Store:
    def __init__(self,path,request,producer_sha,hook=None):
        self.path=Path(path);self.path.mkdir(exist_ok=False);self.request=request;self.producer_sha=producer_sha;self.hook=hook;self.last=None
    def commit(self,events,frontier):
        payload={'schema':'msci-filter-checkpoint-v1','request_sha256':self.request.identity,'producer_sha256':self.producer_sha,'forward_sha256':FORWARD_SHA,'corollary_sha256':COROLLARY_SHA,'sequence':len(events),'events':events,'frontier':[frontier[k].record() for k in sorted(frontier)]}
        raw=canonical(payload);name=f'state-{len(events):05d}-{sha(raw)}.json';target=self.path/name;temp=self.path/(name+'.tmp')
        if target.exists():raise FileExistsError('checkpoint overwrite forbidden')
        with temp.open('xb') as out:out.write(raw);out.flush();os.fsync(out.fileno())
        if self.hook:self.hook('before_commit',payload)
        # Atomic no-replace publication of a fully flushed file; old checkpoints survive.
        os.link(temp,target);temp.unlink();self.last=target
        if self.hook:self.hook('after_commit',payload)
        return target

def run_filter(request,path,provider=None,clock=time.monotonic,hook=None):
    if provider is None:provider=load_forward()
    producer_sha=sha(Path(__file__).read_bytes());store=Store(path,request,producer_sha,hook);events=[];frontier={'r':Cell('r',request.box)};store.commit(events,frontier)
    start=clock();evaluations=0;splits=0;reason='no_pending_cells'
    while True:
        pending=sorted(k for k,c in frontier.items() if c.status=='pending')
        if not pending:break
        if evaluations>=request.budget['max_evaluations']:reason='evaluation_budget';break
        if (clock()-start)*1000>=request.budget['wall_ms']:reason='wall_budget';break
        key=pending[0];cell=frontier[key];frontier[key]=replace(cell,status='inflight');events.append({'kind':'started','cell':key});evaluations+=1;store.commit(events,frontier)
        try:witness=witness_for(cell,request,provider)
        except (provider.DomainError,provider.ResourceBound) as error:
            frontier[key]=replace(cell,status='unsupported');events.append({'kind':'retained','cell':key,'reason':'unsupported_evaluation','error_type':type(error).__name__});store.commit(events,frontier);continue
        if (clock()-start)*1000>=request.budget['wall_ms']:reason='wall_budget';break
        if witness is not None:
            del frontier[key];events.append({'kind':'excluded','cell':key,'witness':witness});store.commit(events,frontier);continue
        widths=[b-a for a,b in cell.box]
        if max(widths)<=request.budget['cell_mesh']:terminal_reason='cell_mesh'
        elif len(key)-1>=request.budget['max_depth']:terminal_reason='depth_budget'
        elif splits>=request.budget['max_splits']:terminal_reason='split_budget'
        else:terminal_reason=None
        if terminal_reason is not None:
            frontier[key]=replace(cell,status=terminal_reason);events.append({'kind':'retained','cell':key,'reason':terminal_reason});store.commit(events,frontier);continue
        axis=max(range(9),key=lambda i:(widths[i],-i));left,right=split_cell(cell,axis)
        del frontier[key];frontier[left.identity]=left;frontier[right.identity]=right;events.append({'kind':'split','cell':key,'axis':axis,'left':left.identity,'right':right.identity});splits+=1;store.commit(events,frontier)
    return {'schema':'bounded-filter-worker-outcome-v1','checkpoint':store.last.name,'stop_reason':reason,'evaluations_started':evaluations,'splits_committed':splits,'cover_certificate_issued':False,'requires_independent_checkpoint_validation':True}
