"""Bounded exact algebra checks; no source recognition or mathematical certification."""
from fractions import Fraction as F
from math import comb
import json

def add(a,b):
    out=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):out[i]+=x
    for i,x in enumerate(b):out[i]+=x
    return out
def lam(r):return r*(r-1)//2
checks=[]
for r in (4,5,8,10):
    p=[F(0)]*(r+1)
    for k in range(r+1):
        for j in range(r-k+1):
            p[k+j]+=comb(r,k)*comb(r-k,j)*(-1)**j*(lam(k)+lam(r-k))
    expected=[F(lam(r)),F(-2*lam(r)),F(2*lam(r))]+[F(0)]*(r-2)
    assert p==expected
    checks.append(f'exact first moment polynomial r={r}')
assert lam(10)+lam(4)-lam(8)-lam(5)==13
assert sum(lam(r)**2 for r in (10,4,8,5))==2945
assert -F(13,2)+F(2945,4)*F(13,2945)==-F(13,4)
checks.append('uniform derivative constants')
# Arbitrary rational positive diagonals check algebra, NOT physical realizability.
cells=[{r:F(20+i,30+i+r) for r in (4,5,8,10)} for i in range(5)]
gaps=[{r:F(30+i,50+i+r) for r in (4,5,8,10)} for i in range(4)]
def product(xs):
    result=F(1)
    for x in xs:result*=x
    return result
def weight(i,a,b):
    return product(cells[j][a] for j in range(i))*product(gaps[j][a] for j in range(i))*product(cells[j][b] for j in range(i+1,5))*product(gaps[j][b] for j in range(i,4))
R=[weight(i,10,5)*cells[i][5]/(weight(i,8,4)*cells[i][4]) for i in range(5)]
for i in range(4):
    expected=cells[i][10]*cells[i][4]/(cells[i][8]*cells[i][5])*gaps[i][10]*gaps[i][4]/(gaps[i][8]*gaps[i][5])
    assert R[i+1]/R[i]==expected
checks.append('actual-product ratio cancellation, four adjacent steps')
for n in range(1,101):
    s=[F((i*i+3*n)%11-5, i+1) for i in range(n)]
    s[-1]-=sum(s)
    r=[F(1,i+1) for i in range(n)]
    assert sum(r[i]*s[i] for i in range(n))==sum((r[k]-r[k+1])*sum(s[:k+1]) for k in range(n-1))
checks.append('Abel identity, lengths1..100 with zero terminal sum')
print(json.dumps({'status':'PASS','checks':checks,'limits':'Exact algebra only; no full source, commutation, global confinement, or master recognition tested.'},indent=2))
