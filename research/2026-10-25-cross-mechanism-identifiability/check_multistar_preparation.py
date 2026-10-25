"""Bounded exact-rational multistar/probe controls, not a general proof."""
from fractions import Fraction as F
from math import comb,factorial
from collections import defaultdict
import json

def group_derivative(t,r):
    k1,k2=t,2*t;N=k1+k2
    states=[(a,b) for a in range(k1+1) for b in range(k2+1)]
    v={c:F(2)**(N-2) if c[0] in (0,k1) and c[1] in (0,k2) else F(0) for c in states}
    for _ in range(r):
        out={}
        for a,b in states:
            c=(a,b);n0=a+b;n1=N-n0
            z=-2*(comb(n0,2)+comb(n1,2))*v[c]
            if a: z+=3*a*(v[(a-1,b)]-v[c])
            if a<k1:z+=3*(k1-a)*(v[(a+1,b)]-v[c])
            if b:z+=3*b*(v[(a,b-1)]-v[c])
            if b<k2:z+=3*(k2-b)*(v[(a,b+1)]-v[c])
            out[c]=z
        v=out
    return sum(F(comb(k1,a)*comb(k2,b),2**N)*v[(a,b)] for a,b in states)

groups=[]
for r in [1,2,3]:
    vals=[group_derivative(t,r) for t in range(r+1,r+2+2*r)]
    for _ in range(2*r): vals=[b-a for a,b in zip(vals,vals[1:])]
    lead=vals[0]/factorial(2*r)
    # w=(1,2), lambda=2: same-deme form=18, different-deme form=10.
    expected=F((-1)**r,2**r)*F(18**r+10**r,2)
    assert lead==expected
    groups.append({'r':r,'leading_coefficient':str(lead),'predicted':str(expected)})

lam=[F(2),F(7)];rates=[[0,F(3)],[F(5),0]]
def row_K(dist):
    out=defaultdict(F)
    for s,p in dist.items():
        hazard=sum(lam[s[a]] for a in range(len(s)) for b in range(a+1,len(s)) if s[a]==s[b])
        out[s]-=p*hazard
        for a in range(len(s)):
            t=list(s);t[a]=1-t[a];rate=rates[s[a]][1-s[a]]
            out[tuple(t)]+=p*rate;out[s]-=p*rate
    return dict(out)
def evolve(poly,dt,degree):
    out=[defaultdict(F) for _ in range(degree+1)]
    for b,d in enumerate(poly):
        v=d
        for a in range(degree-b+1):
            scale=F(dt)**a/factorial(a)
            for s,p in v.items():out[a+b][s]+=scale*p
            v=row_K(v)
    return [dict(x) for x in out]
def merge(poly,a,b):
    out=[]
    for dist in poly:
        d=defaultdict(F)
        for s,p in dist.items():
            if s[a]==s[b]:d[s[:b]+s[b+1:]]+=p*lam[s[a]]
        out.append(dict(d))
    return out
poly=[{(0,0,1,1,1,0):F(1)},{},{}]
for a,b in [(0,2),(0,1),(1,3),(1,2)]:
    poly=merge(evolve(poly,1,2),a,b)
coef=[sum(d.values(),F(0)) for d in poly]
expected=rates[1][0]*lam[0]**2*rates[0][1]*lam[1]**2*1*3
assert coef==[0,0,expected]
print(json.dumps({'arithmetic':'exact fractions.Fraction',
 'scope':'Two-group top-degree controls r=1..3 and one six-lineage two-probe density coefficient; not general verification.',
 'multistar_controls':groups,'probe_initial_locations':[0,0,1,1,1,0],
 'probe_global_merger_times_scaled':[1,2,3,4],
 'probe_density_epsilon_coefficients':list(map(str,coef)),
 'predicted_epsilon_squared_coefficient':str(expected)},indent=2))
