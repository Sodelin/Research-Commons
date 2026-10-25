"""Exact rational finite-dimensional controls; not the all-panel master proof."""
from fractions import Fraction as F
from itertools import product
import json

def zeros(n,m): return [[F(0) for _ in range(m)] for _ in range(n)]
def mul(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),F(0))
             for j in range(len(b[0]))] for i in range(len(a))]
def tensor(a,b):
    return [[a[i][j]*b[k][l] for j in range(len(a[0])) for l in range(len(b[0]))]
            for i in range(len(a)) for k in range(len(b))]
def sym(n):
    states=list(product(range(2),repeat=n)); idx={s:i for i,s in enumerate(states)}
    a=zeros(len(states),len(states))
    for i,s in enumerate(states):
        a[i][i]+=F(1,2); a[i][idx[tuple(1-x for x in s)]]+=F(1,2)
    return a
def killed(n,lam=F(2),m=F(3)):
    states=list(product(range(2),repeat=n)); idx={s:i for i,s in enumerate(states)}
    a=zeros(len(states),len(states))
    for i,s in enumerate(states):
        for k in range(n):
            t=list(s);t[k]=1-t[k];a[i][idx[tuple(t)]]+=m;a[i][i]-=m
        a[i][i]-=lam*sum(s[j]==s[k] for j in range(n) for k in range(j+1,n))
    return a
def delete(n,merge=False):
    states=list(product(range(2),repeat=n)); out=list(product(range(2),repeat=n-1))
    idx={s:i for i,s in enumerate(out)};a=zeros(len(states),len(out))
    for i,s in enumerate(states):
        if not merge: a[i][idx[s[:-1]]]=1
        elif s[0]==s[1]: a[i][idx[(s[0],)+s[2:]]]=2
    return a

records=[]
for n in range(1,5):
    f=sym(n);k=killed(n);alpha=[[F(1,2**n)]*(2**n)]
    assert mul(f,k)==mul(k,f)
    assert mul(alpha,f)==alpha
    row={'n':n,'killed_generator_commutes':True,'independent_uniform_entry_preserved':True}
    if n>=2:
        d=delete(n);c=delete(n,merge=True)
        assert mul(f,d)==mul(d,sym(n-1))
        assert mul(f,c)==mul(c,sym(n-1))
        row.update(deletion_consistent=True,coalescence_operator_intertwines=True)
    records.append(row)
t=sym(1);tt=tensor(t,t);k2=killed(2)
assert sym(2)!=tt
assert mul(k2,tt)!=mul(tt,k2)
lam=F(2);m=F(3);k=[[-2*m-lam,2*m],[2*m,-2*m]]
alpha=[[F(1,2),F(1,2)]];one=[[F(1)],[F(1)]]
d1=mul(mul(alpha,k),one)[0][0]
d2=mul(mul(mul(alpha,k),k),one)[0][0]
assert d1==-lam/2 and d2==lam**2/2 and d2!=d1*d1
print(json.dumps({'arithmetic':'fractions.Fraction exact rational',
  'scope':'Controls n=1..4 only; not a general proof, biological collision or observable-to-hidden bridge.',
  'migration_rate':str(m),'coalescence_rate':str(lam),'checks':records,
  'F2_differs_from_tensor_F1':True,'tensor_F1_fails_killed_intertwining':True,
  'two_lineage_survival_derivatives':[str(d1),str(d2)],
  'one_state_predicted_second_derivative':str(d1*d1)},indent=2))
