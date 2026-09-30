"""Exact feasible-law support masks over the ABSTRACT contrast provider class.

Rows are independently permitted ideal probability vectors with a shared
global mask; this does not decide biological graph/parameter realizability.
Scientific sampling, support and noise promises are trusted inputs.
"""
from fractions import Fraction as F
from dataclasses import dataclass
from itertools import combinations, product
from math import isqrt
from numbers import Integral
from robust_support import Contract, rational, radius_squared


@dataclass(frozen=True)
class FeasibleCertificate:
    status: str
    candidates: tuple[int, ...]
    witnesses: dict
    @property
    def mask(self):
        return self.candidates[0] if self.status == 'CERTIFIED' else None


def upper_root(x, denominator):
    """Exact upward rational square root; error is less than 1/denominator."""
    scaled=x*denominator**2
    k=isqrt(scaled.numerator//scaled.denominator)
    if k*k*scaled.denominator < scaled.numerator:
        k+=1
    return F(k,denominator)


def vertex(constraints):
    # a*p0+b*p1<=c; p2=1-p0-p1. Simplex makes this compact.
    for one,two in combinations(constraints,2):
        a,b,c=one;d,e,f=two;det=a*e-b*d
        if det==0:continue
        x=(c*e-b*f)/det;y=(a*f-c*d)/det
        if all(A*x+B*y<=C for A,B,C in constraints):
            return (x,y,1-x-y)
    return None


def add(constraints, coefficients, bound):
    c0,c1,c2=map(F,coefficients)
    constraints.append((c0-c2,c1-c2,F(bound)-c2))


def row_constraints(box,contract,row,mask):
    lo,hi=box;epsilon=contract.error[row]
    cons=[]
    for i in range(3):
        coeff=[0]*3;coeff[i]=-1;add(cons,coeff,0)
    if sum(lo)>1 or sum(hi)<1 or any(l>u for l,u in zip(lo,hi)):
        return [(F(0),F(0),F(-1))]+cons
    for bits in range(8):
        S=[i for i in range(3) if bits&(1<<i)]
        comp=[i for i in range(3) if i not in S]
        coeff=[int(i in S) for i in range(3)]
        if contract.noise=='tv':
            add(cons,coeff,1-sum(lo[i] for i in comp)+len(S)*epsilon)
            add(cons,[-c for c in coeff],-1+sum(hi[i] for i in comp)+len(S)*epsilon)
        else:
            add(cons,[(1-epsilon)*c for c in coeff],1-sum(lo[i] for i in comp))
    for i in range(3):
        coeff=[0]*3;coeff[i]=1
        if contract.noise=='tv':
            add(cons,coeff,hi[i]+epsilon)
            add(cons,[-c for c in coeff],-lo[i]+epsilon)
        else:
            add(cons,[(1-epsilon)*c for c in coeff],hi[i])
    for t in range(3):
        if not mask&(1<<t):
            for j in range(3):
                coeff=[0]*3;coeff[t]+=1;coeff[j]-=1;add(cons,coeff,0)
    return cons


def observed_witness(p,box,contract,row):
    lo,hi=box;err=contract.error[row]
    if contract.noise=='tv':
        lower=tuple(max(lo[i],p[i]-err) for i in range(3))
        upper=tuple(min(hi[i],p[i]+err) for i in range(3))
    else:
        lower=tuple(max(lo[i],(1-err)*p[i]) for i in range(3));upper=hi
    r=list(lower);remaining=1-sum(r)
    assert remaining>=0 and sum(upper)>=1 and all(lower[i]<=upper[i] for i in range(3))
    for i in range(3):
        extra=min(remaining,upper[i]-r[i]);r[i]+=extra;remaining-=extra
    assert remaining==0
    return tuple(r)


def certify_boxes(boxes,contract):
    boxes=tuple((tuple(rational(x,'box') for x in lo),tuple(rational(x,'box') for x in hi)) for lo,hi in boxes)
    if len(boxes)!=contract.rows or any(len(lo)!=3 or len(hi)!=3 or any(x<0 or x>1 for x in lo+hi) for lo,hi in boxes):
        raise ValueError('one three-coordinate box in [0,1] per row required')
    candidates=[];witnesses={}
    for mask in contract.legal_masks:
        paths={0:[]}
        for e,box in enumerate(boxes):
            base=row_constraints(box,contract,e,mask);options={}
            subsets=[W for W in range(8) if W&mask==W]
            for W in subsets:
                ts=[t for t in range(3) if W&(1<<t)]
                for js in product(range(3),repeat=len(ts)):
                    constraints=list(base)
                    for t,j in zip(ts,js):
                        coeff=[0]*3;coeff[j]+=1;coeff[t]-=1
                        add(constraints,coeff,-contract.gap)
                    p=vertex(constraints)
                    if p is not None:
                        r=observed_witness(p,box,contract,e)
                        options[W]={'p':p,'r':r,'witnesses':tuple(zip(ts,js))}
                        break
            new={}
            for covered,path in paths.items():
                for W,witness in options.items():
                    new.setdefault(covered|W,path+[witness])
            paths=new
            if not paths:break
        if mask in paths:
            candidates.append(mask);witnesses[mask]=paths[mask]
    status='MODEL_INCOMPATIBLE' if not candidates else 'CERTIFIED' if len(candidates)==1 else 'INCONCLUSIVE'
    return FeasibleCertificate(status,tuple(candidates),witnesses)


def certify(counts,contract,queries,delta,*,anytime=True):
    blocks=tuple(tuple(row) for row in counts)
    if len(blocks)!=contract.rows or any(len(row)!=3 or any(isinstance(x,bool) or not isinstance(x,Integral) or x<0 for x in row) for row in blocks):
        raise ValueError('three nonnegative integer counts per row required')
    radius_squared(1,contract.rows,queries,delta,anytime=anytime)
    boxes=[]
    for row in blocks:
        n=int(sum(row))
        if n==0:
            boxes.append(((F(0),)*3,(F(1),)*3));continue
        rho=upper_root(radius_squared(n,contract.rows,queries,delta,anytime=anytime),n)
        center=tuple(F(int(x),n) for x in row)
        boxes.append((tuple(max(0,x-rho) for x in center),tuple(min(1,x+rho) for x in center)))
    return certify_boxes(boxes,contract)


def sharp_distance(gap,rows):
    gap=rational(gap,'gap')
    if not 0<gap<=1 or type(rows) is not int or rows<1:raise ValueError('invalid gap/rows')
    if rows>1:return max(gap/2,gap-F(1,3))
    return max(gap/2,(4*gap-1)/3) if gap<=F(1,2) else gap


if __name__=='__main__':
    if not __debug__:raise RuntimeError('run without -O')
    from feasibility_checks import main
    main()
