"""Exact two-operator controls using actual killed-generator/merger composition.
Terminal vectors are algebraic tests, not asserted hidden observations.
"""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
import json
Q=[[F(-3),F(1),F(2)],[F(3),F(-7),F(4)],[F(5),F(6),F(-11)]];lam=[F(2),F(3),F(7)];d=3
R={(i,j):F(2+2*i+3*j,31) for i,j in product(range(d),repeat=2)}
Rp={(i,j):F(1+i-2*j,17) for i,j in R}
Rpp={(i,j):F(3-2*i+j,19) for i,j in R}
def K(row):
    out=defaultdict(F)
    for s,w in row.items():
        hazard=sum(lam[s[a]] for a in range(len(s)) for b in range(a+1,len(s)) if s[a]==s[b])
        out[s]-=w*hazard
        for a,i in enumerate(s):
            for j in range(d):
                if i!=j:
                    t=list(s);t[a]=j
                    out[tuple(t)]+=w*Q[i][j];out[s]-=w*Q[i][j]
    return {s:w for s,w in out.items() if w}
def collapse(row,start,n):
    out=defaultdict(F)
    for s,w in row.items():
        g=s[start:start+n]
        if all(x==g[0] for x in g):
            out[s[:start+1]+s[start+n:]]+=w*lam[g[0]]**(n-1)
    return dict(out)
def score(row,V):return sum(w*V[s] for s,w in row.items())
def mixed(k,l,i,h):
    initial={(i,)*k+(h,)*l:F(1)}
    c1=lambda row:collapse(row,0,k)
    c2=lambda row:collapse(row,1,l)
    # Derivative of exp(Kpre*t1) C1 exp(Kmid*t2) C2 R(t1+t2).
    return (score(c2(K(c1(K(initial)))),R)+score(c2(c1(K(initial))),Rp)
            +score(c2(K(c1(initial))),Rp)+score(c2(c1(initial)),Rpp))
weights=[1,-3,3,-1];rows=[]
for i,h in product(range(d),repeat=2):
    observed=sum(F(weights[k-1]*weights[l-1])*mixed(k,l,i,h)/lam[i]**(k-1)/lam[h]**(l-1)
                 for k in range(1,5) for l in range(1,5))
    expected=sum(Q[i][j]*Q[h][z]*R[j,z] for j in range(d) for z in range(d) if j!=i and z!=h)
    assert observed==expected,(i,h,observed,expected)
    rows.append({'origins':[i,h],'nested_observation_combination':str(observed),'positive_kernel_product':str(expected)})
print(json.dumps({'scope':'Nine exact nested observation-operator controls,16 star-size pairs each, including all competing hazards and arbitrary first/second future-time derivatives. Not a general theorem or hidden observation access.','largest_raw_panel':8,'checks':rows},indent=2))
