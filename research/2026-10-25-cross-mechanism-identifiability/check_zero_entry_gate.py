"""Exact bounded controls for the zero-entry invisibility gate, not its theorem."""
from fractions import Fraction as F
from math import comb, factorial
import json
p=[F(2,5),F(3,5),F(0)]
Q=[[-7,2,5],[3,-10,7],[11,13,-24]]
lam=[F(3),F(2),F(17)]
def states(k):
    return [(a,b,k-a-b) for a in range(k+1) for b in range(k-a+1)]
def alpha(c):
    v=F(factorial(sum(c)))
    for i,n in enumerate(c):v=v*p[i]**n/factorial(n)
    return v
def apply(v):
    out={}
    for c in v:
        z=-sum(lam[i]*comb(c[i],2) for i in range(3))*v[c]
        for i in range(3):
            for j in range(3):
                if i!=j and c[i]:
                    dest=list(c);dest[i]-=1;dest[j]+=1
                    z+=c[i]*Q[i][j]*(v[tuple(dest)]-v[c])
        out[c]=z
    return out
rows=[]
x=[p[i]*lam[i] for i in range(3)]
u=[sum(p[i]*Q[i][j] for i in range(3)) for j in range(3)]
for k in range(2,8):
    v={c:sum(lam[i]**(k-1) for i in range(3) if c[i]==k) for c in states(k)}
    kv=apply(v)
    a=sum(alpha(c)*v[c] for c in v)
    b=sum(alpha(c)*kv[c] for c in v)
    ea=sum(p[i]*x[i]**(k-1) for i in [0,1])
    eb=k*sum(u[i]*x[i]**(k-1) for i in [0,1])-comb(k,2)*sum(x[i]**k for i in [0,1])
    assert (a,b)==(ea,eb)
    rows.append(dict(k=k,a=str(a),b=str(b)))
v={c:sum(lam[i] for i in range(3) if c[i]==2) for c in states(2)}
kv=apply(v)
exits=[]
for i in [0,1]:
    c=tuple(2 if j==i else 0 for j in range(3))
    gprime=kv[c]
    total=-(gprime+lam[i]**2)/(2*lam[i])
    active=sum(Q[i][j] for j in [0,1] if j!=i)
    ghost=total-active
    assert total==-Q[i][i] and ghost==Q[i][2]
    exits.append(dict(active_state=i,pair_density_derivative=str(gprime),total_exit=str(total),active_exit=str(active),ghost_exit=str(ghost)))
print(json.dumps(dict(scope='Exact bounded checks only; two directly occupied states and one migration-reachable zero-entry state.',p=list(map(str,p)),Q=Q,lambda_=list(map(str,lam)),directly_occupied_count=2,star_checks=rows,exit_checks=exits),indent=2))
