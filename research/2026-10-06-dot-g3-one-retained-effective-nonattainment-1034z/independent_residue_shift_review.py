"""New reviewer-authored rational interval check; no author checker is executed."""
import resource
resource.setrlimit(resource.RLIMIT_CPU, (30, 30))
resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
import sys, json, hashlib, time, itertools
from pathlib import Path
from fractions import Fraction as F
sys.set_int_max_str_digits(1000000)
start = time.monotonic()
root = Path(__file__).resolve().parent
pins = {
    'stage1-result.json': 'c52c9deeeb2a91d2dfb6f5679c845704d160511da3927079b3a97cefdd516e26',
    'stage5-v2-result.json': 'ebd72b9579b63b5f2645bb9199071f0e9f1d3064e069eeaa89899fbb65d3679c',
    'stage6-result.json': '6394667cbf67adaa90a38b94dd6e449f8f656667c712b7902cec0f2f6d122e72',
}
inputs = {}
for name, want in pins.items():
    raw = (root/name).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == want
    inputs[name] = json.loads(raw)

def pt(x):
    x = F(x)
    return (x,x)
def add(a,b): return (a[0]+b[0],a[1]+b[1])
def neg(a): return (-a[1],-a[0])
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    v = [x*y for x in a for y in b]
    return min(v),max(v)
def inv(a):
    assert a[0]*a[1]>0
    return 1/a[1],1/a[0]
def div(a,b): return mul(a,inv(b))
def scale(c,a): return mul(pt(c),a)
def pospow(a,n):
    assert a[0]>=0 and isinstance(n,int) and n>=0
    return a[0]**n,a[1]**n
def total(xs):
    out=pt(0)
    for x in xs: out=add(out,x)
    return out
def mag(a): return max(abs(a[0]),abs(a[1]))
def exact(a):
    assert a[0]==a[1]
    return a[0]
def dump(a): return [str(a[0]),str(a[1])]

lam=(1,3,6,10,15,21)
C=tuple(int(x) for x in inputs['stage1-result.json']['normal'])
d=int(inputs['stage1-result.json']['normal_sum'])
assert d==1016736430620 and sum(C)==d
c=[F(x,d) for x in C]
r=F(1,2)
assert sum(ci*l for ci,l in zip(c,lam))==0
for q in (r,r*r):
    assert sum(ci*(1-q**l) for ci,l in zip(c,lam))==0
    assert sum(ci*l*q**(l-1) for ci,l in zip(c,lam))==0

p0,q0=F('0.605990392211040'),F('0.510276570646996')
radius=F(1,10**12)
box=((p0-radius,p0+radius),(q0-radius,q0+radius))
assert inputs['stage5-v2-result.json']['box']==[dump(x) for x in box]
assert all(0<x[0]<x[1]<1 for x in box)

def derivatives(p,q):
    gs=[pt(0),pt(0)]
    hs=[[pt(0),pt(0)],[pt(0),pt(0)]]
    rows=[];floor=F(1)
    for ci,l in zip(c,lam):
        ql=pospow(q,l)
        # f decreases with p and increases with q on the strict square.
        f=(1-p[1]+p[1]*ql[0],1-p[0]+p[0]*ql[1])
        assert f[0]>0
        floor=min(floor,f[0])
        f2=pospow(f,2)
        one_minus=sub(pt(1),ql)
        hp=div(one_minus,f)
        hq=neg(scale(l,div(mul(p,pospow(q,l-1)),f)))
        hpp=div(pospow(one_minus,2),f2)
        hpq=neg(scale(l,div(pospow(q,l-1),f2)))
        hqq=scale(l*l,div(mul(pospow(p,2),pospow(q,2*l-2)),f2))
        if l>1:
            hqq=sub(hqq,scale(l*(l-1),div(mul(p,pospow(q,l-2)),f)))
        gs=[add(gs[0],scale(ci,hp)),add(gs[1],scale(ci,hq))]
        for i,j,v in ((0,0,hpp),(0,1,hpq),(1,0,hpq),(1,1,hqq)):
            hs[i][j]=add(hs[i][j],scale(ci,v))
        rows.append([pt(l),pt(1-r**l),pt(-l*r**(l-1)),hp,hq])
    return gs,hs,rows,floor

# New independent continuation. Cramer/Leibniz intervals, not author's elimination.
_,J,rows,_=derivatives(*box)
matrix=rows[1:]
def determinant(a):
    result=pt(0)
    for perm in itertools.permutations(range(5)):
        term=pt(1)
        for i,j in enumerate(perm): term=mul(term,a[i][j])
        parity=sum(perm[i]>perm[j] for i in range(5) for j in range(i+1,5))%2
        result=add(result,neg(term) if parity else term)
    return result
minor=determinant(matrix); assert minor[0]>0
rhs=[pt(1-(r*r)**l) for l in lam[1:]]
t=[]
for col in range(5):
    a=[[rhs[i] if j==col else matrix[i][j] for j in range(5)] for i in range(5)]
    t.append(div(determinant(a),minor))
assert t[2][1]<0
B=scale(F(1,8),total(mul(mul(t[i+3],J[i][j]),t[j+3]) for i in range(2) for j in range(2)))
assert B[0]>0
for name,want in pins.items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==want
out={'status':'PASS_NEW_INDEPENDENT_RESIDUE_SHIFT_AND_PRIMARY_BLOCK_SIGN',
     'new_execution':True,'historical_execution_recreated':False,
     'python':sys.version,'inputs_sha256':pins,
     'reviewer_predecessor_code_sha256':'a343741df324a0e774173115bb30bbd99d291b0076bda3e79b3d3ed034d335ff',
     'method':'Exact Fraction interval derivatives and six direct Leibniz determinants with Cramer division; no author checker execution.',
     'minor_interval':dump(minor),'t_intervals':[dump(v) for v in t],
     'retained_quadratic_B_interval':dump(B),'seconds':time.monotonic()-start,
     'scope':'Nonzero residue-shift t_r and positive retained quadratic B at the previously isolated strict critical point; no all-word nonattainment theorem or numerical intensity cutoff.'}
path=root/'independent-residue-shift-result.json'
with path.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(out['status'],flush=True)
print('t intervals',[(float(v[0]),float(v[1])) for v in t],flush=True)
print('B interval',float(B[0]),float(B[1]),flush=True)
print('seconds',out['seconds'],flush=True)
