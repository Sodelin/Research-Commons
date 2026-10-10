#!/usr/bin/env python3
"""Independent stdlib Fraction replay; does not import author's checker."""
from fractions import Fraction as F
from pathlib import Path
import json, hashlib
root=Path(__file__).parent
data=json.loads((root/'baseline-certificate.json').read_text())
L=(1,3,6,10,15,21,28)
J=[]
for l in L:
    row=[F(l),F(1)]
    for p,q in ((F(1,2),F(1,2)),(F(1,2),F(1,3))):
        f=1-p+p*q**l
        row.extend(((1-q**l)/f,-p*l*q**(l-1)/f))
    row.append(F(-int(l==1)))
    J.append(row)
# Solve transpose J * beta = e0 with Fraction-only elimination.
a=[[J[j][i] for j in range(7)]+[F(i==0)] for i in range(7)]
for i in range(7):
    piv=next(j for j in range(i,7) if a[j][i])
    a[i],a[piv]=a[piv],a[i]
    z=a[i][i]; a[i]=[v/z for v in a[i]]
    for j in range(7):
        if j!=i:
            z=a[j][i]; a[j]=[x-z*y for x,y in zip(a[j],a[i])]
beta=[a[i][-1] for i in range(7)]
assert beta==list(map(F,data['b']))
assert [sum(beta[i]*J[i][j] for i in range(7)) for j in range(7)]==[1,0,0,0,0,0,0]
print('PASS independent physical Jacobian, rank seven and inverse baseline row')
Q=list(map(F,data['Q_low_to_high']))
B=[F(0)]*29
for b,l in zip(beta,L): B[0]+=b; B[l]-=b
prod=[F(0)]*29
for i,c in enumerate(Q): prod[i+3]+=c; prod[i+4]-=c
assert prod==B and beta[0]==0 and beta[1]<0 and sum(Q)==1
print('PASS all coefficients of B=x^3(1-x)Q and beta_3<0, Q(1)=1')
def trim(p):
    while p and p[-1]==0:p.pop()
    return p
def rem(a,b):
    a=a[:]
    while len(a)>=len(b):
        c=a[-1]/b[-1]; sh=len(a)-len(b)
        for i,x in enumerate(b):a[i+sh]-=c*x
        trim(a)
    return a
def positive_scale(p):
    # Positive normalization preserves Sturm signs; no sign flips.
    if not p:return p
    den=1
    from math import gcd
    for c in p:den=den*c.denominator//gcd(den,c.denominator)
    z=[int(c*den) for c in p]
    g=0
    for c in z:g=gcd(g,abs(c))
    return [F(c//g) for c in z]
chain=[positive_scale(Q[:]),positive_scale([i*Q[i] for i in range(1,len(Q))])]
while chain[-1]:
    nxt=positive_scale([-c for c in rem(chain[-2],chain[-1])])
    if not nxt:break
    chain.append(nxt)
def value(p,x):
    y=F(0)
    for c in reversed(p):y=y*x+c
    return y
def variations(x):
    signs=[1 if v>0 else -1 for p in chain if (v:=value(p,x))!=0]
    return sum(a!=b for a,b in zip(signs,signs[1:]))
assert Q[0]>0 and value(Q,F(1))>0
v0,v1=variations(F(0)),variations(F(1))
assert v0==v1
print('PASS independent rational Sturm: variations',v0,v1,'and Q>0 on [0,1]')
eps=F(1,1024)
err=sum((abs(b)+1)*F(l*(l-1),3)*eps**(l-3) for b,l in zip(beta,L) if l>=6)
assert err < -beta[1]/4
print('PASS rational epsilon=1/1024 Jensen dominance')
print('Only finite arithmetic checked; analytic/source proof is separate hand review.')

