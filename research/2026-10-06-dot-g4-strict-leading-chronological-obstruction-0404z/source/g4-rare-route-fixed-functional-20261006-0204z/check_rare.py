"""Exact coefficients of one previously frozen full-source functional."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from math import comb, factorial
import hashlib, types, json
BASE=Path(__file__).resolve().parent
PROVIDER=BASE.parent/'g4-complete-weight30-cone-20261005-2332z/check_weight30.py'
PIN='cfaea34e1da58d8a1e14a003bdafc4ceccc074ec2392dc42f689cd4d5440c2f5'
raw=PROVIDER.read_bytes()
if PROVIDER.is_symlink() or hashlib.sha256(raw).hexdigest()!=PIN:raise ValueError('provider identity')
h=types.ModuleType('_accepted_weight30');h.__file__=str(PROVIDER);exec(compile(raw,str(PROVIDER),'exec'),h.__dict__)
m=h.m
COORDS=((9,4,('(((((xx)x)x)x)x)','x','x','x'),30240,-38930),(9,4,('((((xx)(xx))x)x)','x','x','x'),7560,-135),(10,6,('((((xx)x)x)x)','x','x','x','x','x'),15120,2431))
def add(p,key,v):
    if v:p[key]=p.get(key,F(0))+v
    if key in p and not p[key]:del p[key]
def mul(p,q,cap=5):
    out={}
    for (e,r,z),v in p.items():
        for (f,s,w),u in q.items():
            if e+f<=cap:add(out,(e+f,r+s,z+w),v*u)
    return out

def pair_series(cap):
    out={}
    for p in range(cap+1):
        for shift,c in ((0,1),(1,-2),(2,1)):
            if p+shift<=cap:add(out,(p+shift,0,p),F(c*(-1)**p,factorial(p)))
    if cap>=1:add(out,(1,0,0),F(2))
    if cap>=2:add(out,(2,1,0),F(1));add(out,(2,0,0),F(-2))
    return out

def inverse_pair(power,cap):
    b=pair_series(cap);add(b,(0,0,0),F(-1));term={(0,0,0):F(1)};out={};coef=F(1)
    for l in range(cap+1):
        for key,v in term.items():add(out,key,coef*v)
        term=mul(term,b,cap);coef=coef*F(-power-l,l+1)
    return out

def split_coeffs(ctx,v,cap):
    rows=[[F(0)]*len(ctx.colours) for _ in range(cap+1)]
    for value,f in zip(v,ctx.states):
        if not value:continue
        k=len(f)
        for bits in product((0,1),repeat=k):
            j=sum(bits)
            if j>cap:continue
            rare=tuple(t for t,b in zip(f,bits) if b);common=tuple(t for t,b in zip(f,bits) if not b)
            ix=ctx.cids[rare,common]
            for l in range(min(k-j,cap-j)+1):rows[j+l][ix]+=value*((-1)**l)*comb(k-j,l)
    return rows

def rare_project(row,q,rate,rates):
    out=list(row)
    for other in rates:
        if other!=rate:out=[(x+other*y)/(other-rate) for x,y in zip(m.apply(out,q),out)]
    if m.apply(out,q)!=[-rate*x for x in out]:raise ValueError('rare-arm projector on retained row')
    return out

def terminal_column(ctx,shape,multiplicity):
    if shape not in ctx.ids or m.orbit_size(shape)!=multiplicity:raise ValueError('fixed coordinate')
    v=[F(0)]*len(ctx.states);v[ctx.ids[shape]]=F(1,multiplicity);lj=comb(ctx.bottom,2)
    for k in range(ctx.bottom,ctx.n+1):
        if k==ctx.bottom:continue
        lk=comb(k,2)
        qv=[sum(x*v[j] for j,x in row.items()) for row in ctx.q]
        v=[(x+lk*y)/(lk-lj) for x,y in zip(qv,v)]
    return [v[ctx.ids[tuple(sorted(a+b))]] for a,b in ctx.colours]

def coefficients(ctx,coords,cap):
    left=ctx.project(ctx.e,ctx.n);split=split_coeffs(ctx,left,cap)
    rates=tuple(sorted({comb(k,2) for k in range(cap+1)}));cols=[terminal_column(ctx,c[2],c[3]) for c in coords]
    answer=[{} for _ in coords]
    for a,start in enumerate(split):
        if not any(start):continue
        recovered=[F(0)]*len(start)
        for rate in rates:
            row=rare_project(start,ctx.ql,rate,rates)
            recovered=[x+y for x,y in zip(recovered,row)]
            for p in range(cap-a+1):
                for out,col in zip(answer,cols):add(out,(a+p,rate,p),sum(x*y for x,y in zip(row,col))/factorial(p))
                if p<cap-a:row=m.apply(row,ctx.qr)
        if recovered!=start:raise ValueError('rare-arm spectral completeness')
    normal=inverse_pair(comb(ctx.bottom,2),cap)
    return [mul(out,normal,cap) for out in answer]

def serialized(p):return [{'epsilon_degree':e,'rho_degree':r,'z_degree':z,'coefficient':str(v)} for (e,r,z),v in sorted(p.items())]
def run_degree(cap):
    total={};records=[]
    for n,j in ((9,4),(10,6)):
        coords=[c for c in COORDS if c[:2]==(n,j)];ctx=h.Quotient(n,j)
        for coord,p in zip(coords,coefficients(ctx,coords,cap)):
            for key,v in p.items():add(total,key,coord[4]*v)
            records.append({'input_arity':n,'output_roots':j,'shape':list(coord[2]),'multiplicity':coord[3],'weight':coord[4],'coefficients':serialized(p)})
    if any(e<=3 for e,r,z in total):raise ValueError('accepted lower-order identities failed')
    return total,records

def run():
    p4,records4=run_degree(4)
    out={'schema':'rare-route-fixed-functional-v1','provider_sha256':PIN,'stage4':{'coordinates':records4,'functional':serialized(p4)},'original_G4_closed':False,'sign_theorem_claimed':False,'other_functionals_or_caps_examined':False}
    if p4:
        out.update(decision='DEGREE4_PREMISE_FALSE_STOP',stage5_executed=False);return out
    p5,records5=run_degree(5)
    out.update(decision='DEGREE4_ZERO_DEGREE5_POLYNOMIAL_FOR_REVIEW',stage5_executed=True,stage5={'coordinates':records5,'functional':serialized(p5)})
    return out
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
