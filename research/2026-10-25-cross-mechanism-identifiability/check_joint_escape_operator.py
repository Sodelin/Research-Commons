"""Exact row-generator controls for the legal joint escape response identity.
Arbitrary terminal-vector controls validate algebra, not hidden observation access.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
import json
Q=[[F(-3),F(1),F(2)],[F(3),F(-7),F(4)],[F(5),F(6),F(-11)]]
lam=[F(2),F(3),F(7)];d=len(lam)

def terminal(k,s,R):
    group=s[:k]
    if any(x!=group[0] for x in group):return F(0)
    return lam[group[0]]**(k-1)*R[(group[0],)+s[k:]]
def derivative(k,i,b,R,Rdot):
    s=(i,)*k+b;v=terminal(k,s,R)
    kill=sum(lam[s[a]] for a in range(len(s)) for z in range(a+1,len(s)) if s[a]==s[z])
    out=-kill*v
    for a,x in enumerate(s):
        for y in range(d):
            if y!=x:
                dest=list(s);dest[a]=y
                out+=Q[x][y]*(terminal(k,tuple(dest),R)-v)
    out+=lam[i]**(k-1)*Rdot[(i,)+b]
    return out
rows=[]
for m in [0,1,2]:
    ss=list(product(range(d),repeat=m+1))
    R={s:F(1+sum((i+1)*(x+1) for i,x in enumerate(s)),31) for s in ss}
    Rdot={s:F(sum((-1)**i*(x+2) for i,x in enumerate(s)),17) for s in ss}
    for i in range(d):
        for b in product(range(d),repeat=m):
            vals=[derivative(k,i,b,R,Rdot)/lam[i]**(k-1) for k in range(1,5)]
            actual=vals[0]-3*vals[1]+3*vals[2]-vals[3]
            expected=sum(Q[i][j]*R[(j,)+b] for j in range(d) if j!=i)
            assert actual==expected
            rows.append({'mains':m,'origin':i,'main_tuple':b,'escape_response':str(actual)})
# Same expression on constant future response recovers total exit.
for i in range(d):
    R={(j,):F(1) for j in range(d)};Rdot={(j,):F(0) for j in range(d)}
    vals=[derivative(k,i,(),R,Rdot)/lam[i]**(k-1) for k in range(1,5)]
    assert vals[0]-3*vals[1]+3*vals[2]-vals[3]==-Q[i][i]
print(json.dumps({'scope':'Exact algebraic controls for arbitrary terminal responses and time derivatives; not empirical or hidden-state observation access.','checks':len(rows),'constant_response_checks':d,'rows':rows},indent=2))
