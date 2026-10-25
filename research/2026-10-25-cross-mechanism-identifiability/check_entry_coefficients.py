"""Exact finite coefficient checks; no full identifiability or formal certificate."""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
import json

p=[F(1,2),F(1,3),F(1,6)]
Q=[[-3,1,2],[3,-4,1],[2,2,-4]]

def counts(k):
    return [(a,b,k-a-b) for a in range(k+1) for b in range(k-a+1)]
def alpha(c):
    v=F(factorial(sum(c)))
    for i,n in enumerate(c): v=v*p[i]**n/factorial(n)
    return v
def apply_K(v,states,lam):
    out={}
    for c in states:
        z=-sum(lam[i]*comb(c[i],2) for i in range(3))*v[c]
        for i in range(3):
            for j in range(3):
                if i!=j and c[i]:
                    dest=list(c);dest[i]-=1;dest[j]+=1
                    z+=c[i]*Q[i][j]*(v[tuple(dest)]-v[c])
        out[c]=z
    return out
def derivative(k,r,lam):
    states=counts(k)
    v={c:sum(lam[i]**(k-1) for i in range(3) if c[i]==k) for c in states}
    for _ in range(r):v=apply_K(v,states,lam)
    return sum(alpha(c)*v[c] for c in states)

rows=[]
for name,lam in [('distinct_x',[F(2),F(6),F(18)]),('collided_x',[F(2),F(3),F(6)])]:
    x=[p[i]*lam[i] for i in range(3)]
    u=[sum(p[i]*Q[i][j] for i in range(3)) for j in range(3)]
    for k in range(2,7):
        a=derivative(k,0,lam);b=derivative(k,1,lam)
        assert a==sum(p[i]*x[i]**(k-1) for i in range(3))
        expected=k*sum(u[i]*x[i]**(k-1) for i in range(3))-comb(k,2)*sum(xi**k for xi in x)
        assert b==expected
        rows.append(dict(case=name,k=k,a=str(a),b=str(b)))

# For three ordered blocks (i,i,j), C_13 C_(13),2 1 is lambda^2 on pure states.
lam=[F(2),F(6),F(18)];states=counts(3)
v={c:sum(lam[i]**2 for i in range(3) if c[i]==3) for c in states}
kv=apply_K(v,states,lam)
for i in range(3):
    for j in range(3):
        if i!=j:
            c=[0,0,0];c[i]=2;c[j]=1
            assert kv[tuple(c)]==Q[j][i]*lam[i]**2

# Candidate higher-derivative polynomial-leading-term control, all x_i=1.
leading=[];lam=[F(2),F(3),F(6)]
for r in [1,2,3]:
    vals=[derivative(k,r,lam) for k in range(r+1,r+2+2*r)]
    for _ in range(2*r):vals=[b-a for a,b in zip(vals,vals[1:])]
    lead=vals[0]/factorial(2*r)
    expected=F((-1)**r,2**r)*sum(p[i]*lam[i]**r for i in range(3))
    assert lead==expected
    leading.append(dict(order=r,leading_coefficient=str(lead),candidate_expected=str(expected)))
print(json.dumps(dict(arithmetic='exact fractions.Fraction',p=list(map(str,p)),Q=Q,
    scope='Bounded coefficient and directional-derivative controls; higher-order formula remains candidate.',
    star_checks=rows,directed_three_block_checks=6,higher_derivative_controls=leading),indent=2))
