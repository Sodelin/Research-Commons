"""Exact two-group top-degree controls with an initially absent migration-reachable deme."""
from fractions import Fraction as F
from math import comb,factorial
import json
Q=[[-3,1,2],[3,-7,4],[5,6,-11]];lam=[2,2,7]
def counts(k):return [(a,b,k-a-b) for a in range(k+1) for b in range(k-a+1)]
def pure(c):return next((i for i,n in enumerate(c) if n==sum(c)),None)
def coeff(t,r):
    k,l=t,2*t;cs=counts(k);ds=counts(l);ss=[(c,d) for c in cs for d in ds]
    v={s:(lam[pure(s[0])]**(k-1)*lam[pure(s[1])]**(l-1) if pure(s[0]) is not None and pure(s[1]) is not None else 0) for s in ss}
    for _ in range(r):
        out={}
        for s in ss:
            totals=[s[0][i]+s[1][i] for i in range(3)]
            z=-sum(lam[i]*comb(totals[i],2) for i in range(3))*v[s]
            for g in range(2):
                c=s[g]
                for i in range(3):
                    if c[i]:
                        for j in range(3):
                            if i!=j:
                                dest=list(c);dest[i]-=1;dest[j]+=1
                                ss2=(tuple(dest),s[1]) if g==0 else (s[0],tuple(dest))
                                z+=c[i]*Q[i][j]*(v[ss2]-v[s])
            out[s]=z
        v=out
    numerator=sum(comb(k,a)*comb(l,b)*v[((a,k-a,0),(b,l-b,0))] for a in range(k+1) for b in range(l+1))
    return F(numerator,2**(k+l))
rows=[]
for r in [1,2]:
    ts=list(range(r+1,3*r+2));vals=[coeff(t,r) for t in ts]
    for _ in range(2*r):vals=[b-a for a,b in zip(vals,vals[1:])]
    lead=vals[0]/factorial(2*r)
    expected=F((-1)**r,2**r)*F(18**r+10**r,2)
    assert lead==expected
    rows.append({'order':r,'t_grid':ts,'leading_coefficient':str(lead),'predicted_active_partition_coefficient':str(expected),'largest_total_sample':3*max(ts)})
print(json.dumps({'scope':'Bounded exact two-group support-only coefficient checks, not arbitrary multistar/future-response verification.','initial_p':['1/2','1/2','0'],'lambda':lam,'Q':Q,'checks':rows},indent=2))
