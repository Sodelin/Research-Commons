"""Exact symbolic source coefficients for the fixed full-forest functional."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
from math import comb
import hashlib,importlib.util,json
BASE=Path(__file__).resolve().parent
PROVIDER=BASE.parent/'g4-lossless-resonance-20261005-2042z/lossless_resonance.py'
PIN='3bbbbe54d4c28abe2515c14143e9d83629e650ba0ac0df411457dec7fa17c9be'
if PROVIDER.is_symlink():raise ValueError('provider link')
RAW=PROVIDER.read_bytes()
if hashlib.sha256(RAW).hexdigest()!=PIN:raise ValueError('provider pin')
spec=importlib.util.spec_from_file_location('_lossless_provider',PROVIDER);m=importlib.util.module_from_spec(spec);exec(compile(RAW,str(PROVIDER),'exec'),m.__dict__)

def coloured(n):
    if not 1<=n<=9:raise ValueError('fixed cap')
    states=tuple((a,b) for k in range(n+1) for a in m.forests(k) for b in m.forests(n-k));ids={v:i for i,v in enumerate(states)}
    if len(states)>4096:raise ValueError('coloured state ceiling')
    qs=[]
    for side in (0,1):
        mat=[]
        for a,b in states:
            f=(a,b)[side];row={ids[a,b]:F(-comb(len(f),2))}
            for i,j in combinations(range(len(f)),2):
                ff=tuple(sorted([m.tree(f[i],f[j])]+[f[k] for k in range(len(f)) if k not in (i,j)]));state=(ff,b) if side==0 else (a,ff);z=ids[state];row[z]=row.get(z,F(0))+1
            assert sum(row.values())==0;mat.append({i:v for i,v in row.items() if v})
        qs.append(mat)
    return states,ids,qs[0],qs[1]

def split(v,states,ids):
    out=[F(0)]*len(ids)
    for value,f in zip(v,states):
        if not value:continue
        for bits in product((0,1),repeat=len(f)):
            a=tuple(t for t,b in zip(f,bits) if b==0);b=tuple(t for t,b in zip(f,bits) if b==1);out[ids[a,b]]+=value/F(2**len(f))
    return out

def apply_col(q,v):return [sum(x*v[j] for j,x in row.items()) for row in q]
def project_col(v,j,q,n):
    out=list(v);lj=comb(j,2)
    for k in range(1,n+1):
        if k!=j:
            lk=comb(k,2);a=apply_col(q,out);out=[(x+lk*y)/(lk-lj) for x,y in zip(a,out)]
    return out

def binomial_next(row,q,k):
    # From row*binom(-Q,k) to row*binom(-Q,k+1).
    applied=m.apply(row,q);return [(-x-k*y)/(k+1) for x,y in zip(applied,row)]

def expansion(z,order):
    # z[(r,s)] multiplies (-a e-b e^(3/2))^r (-a e+b e^(3/2))^s.
    out={}
    for (r,s),value in z.items():
        for i in range(r+1):
            for j in range(s+1):
                aa=r+s-i-j;bb=i+j;degree2=2*aa+3*bb
                if degree2>2*order:continue
                key=(degree2,aa,bb);out[key]=out.get(key,F(0))+value*comb(r,i)*comb(s,j)*(-1)**(r+s-j)
    odd={k:v for k,v in out.items() if k[2]%2 and v}
    if odd:raise ValueError('arm-symmetry odd coefficient did not cancel')
    return {(d//2,a,b//2):v for (d,a,b),v in out.items() if not b%2 and v}

def compute(n,weights,order):
    if not 0<=order<=6:raise ValueError('jet order cap')
    states,ids,q,r=m.build(n);cs,ci,ql,qr=coloured(n)
    e=[F(0)]*len(states);e[ids[('x',)*n]]=F(1);left=m.project(e,n,q,n);sv=split(left,states,ci)
    w=[F(0)]*len(states)
    for i,x in weights.items():w[i]=F(x)
    right=project_col(w,4 if n>=4 else n,q,n);cw=[right[ids[tuple(sorted(a+b))]] for a,b in cs]
    vals={};vr=sv
    for r in range(order+1):
        row=vr
        for s in range(order-r+1):
            vals[r,s]=sum(x*y for x,y in zip(row,cw))
            if s<order-r:row=binomial_next(row,qr,s)
        if r<order:vr=binomial_next(vr,ql,r)
    raw=expansion(vals,order);normal={};lam=comb(4 if n>=4 else n,2)
    for (degree,a,b),v in raw.items():
        for k in range(order-degree+1):
            coeff=F(comb(lam+k-1,k),2**k) if lam else F(k==0)
            key=(degree+k,a+k,b);normal[key]=normal.get(key,F(0))+v*coeff
    normal={k:v for k,v in normal.items() if v}
    return states,cs,vals,raw,normal

def run():
    states,cs,vals,raw,normal=compute(9,{0:245,1:146,2:68},6)
    if any(k[0]<=3 for k in normal):raise ValueError('known lower projection failed')
    coeff={str(k):{f'a^{k-3*j} w^{j}':str(normal.get((k,k-3*j,j),F(0))) for j in range(k//3+1)} for k in range(4,7)}
    p={f'a^{6-3*j} w^{j}':normal.get((6,6-3*j,j),F(0))+v for j,v in enumerate([F(91,16),-F(273,4),F(819,4)])}
    return {'schema':'coherent-sixth-source-scalar-coefficients-v1','source_family':'x=1-a*e-sqrt(w)*e^(3/2), y=1-a*e+sqrt(w)*e^(3/2), g=1/2; a,w>0','normalization':'U=B E(b2^-1), b2=1-a*e/2; algebraic normalization only','functional':'245,146,68 on orbit masses0,1,2 of initial P9 U P4','unlabelled_full_forest_states':len(states),'two_colour_states':len(cs),'source_provider_sha256':PIN,'arm_binomial_scalar_coefficients':{f'{r},{s}':str(v) for (r,s),v in vals.items()},'raw_coefficients':[{'e_degree':k,'a_power':a,'w_power':b,'coefficient':str(v)} for (k,a,b),v in sorted(raw.items())],'normalized_coefficients':coeff,'known_grades_zero_through':3,'scalar_grades4_and5_identically_zero':not any(k[0] in (4,5) for k in normal),'r3_coefficient':'3*w/8-a^3/16','constant_parameter_sixth_balance_polynomial':{k:str(v) for k,v in p.items()},'coherent_scope':'higher parameter/placement corrections may be dropped only if lower scalar grades vanish identically; full vector cancellation still required','sign_claimed':False,'master_G4_closed':False}
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
