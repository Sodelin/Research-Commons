"""Bounded exact controls for partial-entry coefficients and invariant expansion.
No full inference implementation or general theorem certificate.
"""
from fractions import Fraction as F
from math import comb,factorial
from itertools import permutations,product
import json

def states(k):return [(a,b,k-a-b) for a in range(k+1) for b in range(k-a+1)]
p=[F(1,2),F(1,2),F(0)];lam=[F(2),F(2),F(7)]
Q=[[-3,1,2],[3,-7,4],[5,6,-11]]
def derivative(k,r):
    ss=states(k);v={c:sum(lam[i]**(k-1) for i in range(3) if c[i]==k) for c in ss}
    for _ in range(r):
        out={}
        for c in ss:
            z=-sum(lam[i]*comb(c[i],2) for i in range(3))*v[c]
            for i in range(3):
                for j in range(3):
                    if i!=j and c[i]:
                        dst=list(c);dst[i]-=1;dst[j]+=1
                        z+=c[i]*Q[i][j]*(v[tuple(dst)]-v[c])
            out[c]=z
        v=out
    total=F(0)
    for c in ss:
        a=F(factorial(k))
        for i in range(3):a=a*p[i]**c[i]/factorial(c[i])
        total+=a*v[c]
    return total
coef=[]
for r in range(1,5):
    values=[derivative(k,r) for k in range(r+1,3*r+2)]
    for _ in range(2*r):values=[b-a for a,b in zip(values,values[1:])]
    lead=values[0]/factorial(2*r)
    expected=F((-1)**r,2**r)*sum(p[i]*lam[i]**r for i in [0,1])
    assert lead==expected
    coef.append({'order':r,'leading_coefficient':str(lead),'sample_max':3*r+1})
# Irreducible four-state example with a single initially occupied state.
Q4=[[F(-2),F(2),F(0),F(0)],[F(1),F(-4),F(3),F(0)],[F(0),F(2),F(-7),F(5)],[F(0),F(1),F(0),F(-1)]]
kappa=F(1);S={0};stages=[]
while True:
    A=sum(-Q4[i][i] for i in S)
    B=sum(Q4[i][j] for i in S for j in S if i!=j)
    leak=A-B
    Z=kappa*len(S)+A
    weights=[(kappa*int(j in S)+sum(Q4[i][j] for i in S if i!=j))/Z for j in range(4)]
    assert sum(weights)==1
    # Same joint two-block expansion in every active-label frame, no per-block relabelling.
    joint={(j,k):F(0) for j,k in product(range(4),repeat=2)}
    perms=list(permutations(sorted(S)))
    for perm in perms:
        for x,y in product(range(len(S)),repeat=2):
            i,h=perm[x],perm[y]
            wi=[kappa*int(j==i)+(Q4[i][j] if j!=i else 0) for j in range(4)]
            wh=[kappa*int(j==h)+(Q4[h][j] if j!=h else 0) for j in range(4)]
            for j,k in joint:joint[j,k]+=wi[j]*wh[k]/Z**2/len(perms)
    assert all(joint[j,k]==weights[j]*weights[k] for j,k in joint)
    stages.append({'support':sorted(S),'total_exit':str(A),'internal_exit':str(B),'leakage':str(leak),'expanded_entry':list(map(str,weights)),'permutations_checked':len(perms)})
    if leak==0:break
    S2={j for j in range(4) if weights[j]>0}
    assert S<S2;S=S2
assert S==set(range(4)) and len(stages)==4
print(json.dumps({'scope':'Exact partial-entry top-degree and invariant two-block support-expansion controls only. No observed-data inference or full proof verification.','partial_entry_coefficients':coef,'expansion_stages':stages},indent=2))
