"""One exact all-arity quartic identity decision via the reviewed locality bound."""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import hashlib,json,types
BASE=Path(__file__).resolve().parent
PROVIDER=BASE.parent/'g4-coherent-sixth-jet-20261005-2058z/source_coefficients.py'
PIN='aed745dd0d3fc37a8b5eef838f000675ad3fb6c37a66116f14eacfe01192f998'
CORE=BASE.parent/'g4-lossless-resonance-20261005-2042z/lossless_resonance.py'
CORE_PIN='3bbbbe54d4c28abe2515c14143e9d83629e650ba0ac0df411457dec7fa17c9be'
def authenticated_module(path,pin,name):
    if path.is_symlink():raise ValueError('provider symlink')
    raw=path.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=pin:raise ValueError('provider hash')
    mod=types.ModuleType(name);mod.__file__=str(path)
    exec(compile(raw,str(path),'exec'),mod.__dict__)
    return mod
if CORE.is_symlink() or hashlib.sha256(CORE.read_bytes()).hexdigest()!=CORE_PIN:raise ValueError('core pin')
c=authenticated_module(PROVIDER,PIN,'_quartic_source_provider');m=c.m

def kappa(r,s,j):
    return sum(comb(r,i)*comb(s,2*j-i)*(-1)**(2*j-i) for i in range(r+1) if 0<=2*j-i<=s)

def positive_binomial(row,q,l):
    out=list(row)
    for k in range(l):
        applied=m.apply(out,q);out=[(x-k*y)/(k+1) for x,y in zip(applied,out)]
    return out

def forget(row,colours,ids):
    out=[F(0)]*len(ids)
    for value,(a,b) in zip(row,colours):out[ids[tuple(sorted(a+b))]]+=value
    return out

def coefficient(d,j,arm,q):
    if d!=4 or j not in (0,1):raise ValueError('only frozen quartic coefficients')
    out=[F(0)]*len(q)
    for l in range(d-3*j+1):
        k=d-j-l
        for r in range(k+1):
            s=k-r;factor=F((-1)**(d-j)*kappa(r,s,j),2**l)
            if factor:
                row=positive_binomial(arm[r,s],q,l)
                out=[x+factor*y for x,y in zip(out,row)]
    return out

def check_arity(n):
    if not 0<=n<=8:raise ValueError('declared arity range')
    if n==0:
        states=((),);h0=h1=rr=comm=res=[F(0)];colour_count=1
    else:
        states,ids,q,r=m.build(n)
        if len(states)>2000:raise ValueError('complete state ceiling')
        colours,ci,ql,qr=c.coloured(n);colour_count=len(colours)
        e=[F(0)]*len(states);e[ids[('x',)*n]]=F(1)
        split=c.split(e,states,ci);arm={};left=split
        for i in range(5):
            row=left
            for j in range(5-i):
                arm[i,j]=forget(row,colours,ids)
                if j<4-i:row=c.binomial_next(row,qr,j)
            if i<4:left=c.binomial_next(left,ql,i)
        h0=coefficient(4,0,arm,q);h1=coefficient(4,1,arm,q)
        rr=m.apply(e,r);qrrow=m.apply(m.apply(e,q),r);rqrow=m.apply(rr,q)
        comm=[x-y for x,y in zip(qrrow,rqrow)]
        res=[a+b/8+(9*d+z)/128 for a,b,d,z in zip(h0,h1,rr,comm)]
    encode=lambda row:list(map(str,row))
    return {'arity':n,'complete_orbit_count':len(states),'two_colour_count':colour_count,
            'orbits':[{'shape':list(f),'labelled_multiplicity':m.orbit_size(f)} for f in states],
            'H40':encode(h0),'H41':encode(h1),'R3':encode(rr),'commutator_QR_minus_RQ':encode(comm),
            'residual':encode(res),'identity_holds':not any(res),
            'first_nonzero_orbit':next((i for i,v in enumerate(res) if v),None)}

def run():
    records=[]
    for n in range(9):
        record=check_arity(n);records.append(record)
        if not record['identity_holds']:break
    passed=len(records)==9 and all(r['identity_holds'] for r in records)
    return {'schema':'all-arity-quartic-locality-decision-v1','source_provider_sha256':PIN,'forest_provider_sha256':CORE_PIN,
            'candidate_identity':'H40 + H41/8 = -(9R3 + Q R3 - R3 Q)/128',
            'arities_checked':[r['arity'] for r in records],'records':records,
            'decision':'ALL_ARITY_IDENTITY_VIA_LOCALITY' if passed else 'CANDIDATE_IDENTITY_FALSE',
            'all_arity_implication_requires_reviewed_support_bound':8,
            'coefficient_retuning_permitted':False,'full_formal_return_constructed':False,'original_G4_closed':False}
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
