"""Independent standard-library exact check: no SymPy or numerical arithmetic."""
from fractions import Fraction as Q
from functools import reduce
from math import gcd, lcm
from pathlib import Path
ROOT=Path(__file__).resolve().parent
L=(1,3,6,10,15,21,28)
def data(q):
    z=[q**k for k in L]
    return ([2*(1-x)/(1+x) for x in z],
            [k*x/(1+x) for k,x in zip(L,z)],
            [4*(1-x)**2/(1+x)**2 for x in z],
            [4*k*x/(1+x)**2 for k,x in zip(L,z)],
            [-k*k*x/(1+x)**2 for k,x in zip(L,z)])
D=[data(Q(1,2)),data(Q(1,3))]
M=[[Q(x) for x in L]]+[r for d in D for r in d[:2]]
A=[r[:] for r in M]; piv=[]; nr=0
for j in range(7):
    i=next((i for i in range(nr,5) if A[i][j]),None)
    if i is None:continue
    A[nr],A[i]=A[i],A[nr];v=A[nr][j];A[nr]=[x/v for x in A[nr]]
    for i in range(5):
        if i!=nr:
            v=A[i][j];A[i]=[x-v*y for x,y in zip(A[i],A[nr])]
    piv.append(j);nr+=1
    if nr==5:break
assert piv==[0,1,2,3,4]
bs=[]
for j in [5,6]:
    v=[Q(0)]*7;v[j]=Q(1)
    for i,k in enumerate(piv):v[k]=-A[i][j]
    assert all(sum(x*y for x,y in zip(r,v))==0 for r in M)
    bs.append(v)
u,v=bs
print('PASS head tangent rank 5; normal basis final coordinates (1,0),(0,1)')
dot=lambda a,b:sum(x*y for x,y in zip(a,b))
hu=[dot(u,d) for d in D[1][2:]];hv=[dot(v,d) for d in D[1][2:]]
n=[hu[1]*hv[2]-hu[2]*hv[1],hu[2]*hv[0]-hu[0]*hv[2],hu[0]*hv[1]-hu[1]*hv[0]]
assert n[2]!=0
alpha,beta=n[0]/n[2],n[1]/n[2]
assert all(alpha*h[0]+beta*h[1]+h[2]==0 for h in [hu,hv])
assert alpha>Q(7,4) and -Q(7,5)<beta<0
assert alpha-beta*beta/4>Q(63,50)
print('PASS Hessian injectivity; Htt=-alpha Hpp-beta Hpt; alpha>7/4; -7/5<beta<0')
print('alpha',alpha);print('beta',beta);print('injection determinant',n[2])
# Integer polynomials use ascending coefficients. All normalizations are positive.
def trim(a):
    while len(a)>1 and not a[-1]:a.pop()
    return a

def prim(a):
    a=trim(a[:]);g=reduce(gcd,(abs(x) for x in a),0)
    return [x//g for x in a] if g else [0]
def ints(a):
    d=reduce(lcm,(x.denominator for x in a),1)
    return prim([int(x*d) for x in a])
def add(a,b,sgn=1):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=sgn*x
    return trim(c)
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)
def der(a):return trim([i*a[i] for i in range(1,len(a))])
def ev(a,x):
    v=Q(0)
    for k in reversed(a):v=v*x+k
    return v
def exactdiv(a,b):
    a=list(map(Q,a));out=[Q(0)]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b) and a!=[0]:
        k=len(a)-len(b);t=a[-1]/b[-1];out[k]+=t
        for i,y in enumerate(b):a[i+k]-=t*y
        trim(a)
    assert a==[0]
    return ints(out)
def prem_pos(a,b):
    # Each elimination scales the true rational remainder by a positive number.
    a=prim(a)
    while len(a)>=len(b) and a!=[0]:
        k=len(a)-len(b);t=a[-1]*(1 if b[-1]>0 else -1);s=abs(b[-1])
        a=[x*s for x in a]
        for i,y in enumerate(b):a[i+k]-=t*y
        a=prim(a)
    return a
Fs=[]
for c in bs:
    f=[Q(0)]*29;f[0]=sum(c)
    for k,x in zip(L,c):f[k]-=x
    Fs.append(ints(f))
Gs=[exactdiv(f,[1,-2,1]) for f in Fs]
W=prim(add(mul(Gs[0],der(Gs[1])),mul(der(Gs[0]),Gs[1]),-1))
assert [len(g)-1 for g in Gs]==[19,26] and len(W)-1==44
chain=[W,prim(der(W))]
while len(chain[-1])>1:
    r=prem_pos(chain[-2],chain[-1]);assert r!=[0]
    chain.append(prim([-x for x in r]))
assert len(chain[-1])==1 and chain[-1][0]!=0
print('PASS W degree 44 and squarefree; Sturm chain degrees',[len(p)-1 for p in chain])
def variation(x):
    vals=[ev(p,x) for p in chain]
    assert vals[0]!=0
    sig=[1 if y>0 else -1 for y in vals if y]
    return sum(a!=b for a,b in zip(sig,sig[1:]))
intervals=[(Q(121,500),Q(61,250)),(Q(37,125),Q(149,500)),(Q(223,500),Q(56,125)),(Q(501,1000),Q(503,1000))]
assert variation(Q(0))-variation(Q(1))==4
print('Sturm endpoint variations 0,1:',variation(Q(0)),variation(Q(1)))
for a,b in intervals:
    va,vb=variation(a),variation(b);assert va-vb==1
    print('isolating interval',a,b,'variations',va,vb)
for a,b in intervals:
    for c,d in intervals:assert b*b<c or d<a*a
print('PASS every squared isolating interval disjoint from all four isolating intervals')
assert all(b*b<intervals[0][0] for a,b in intervals[:3])
assert intervals[0][1]<intervals[3][0]**2<intervals[3][1]**2<intervals[1][0]
print('PASS no r in (0,1) with W(r)=W(r^2)=0')
(ROOT/'exact-polynomials.json').write_text(__import__('json').dumps({'Lambda':L,'Gu':Gs[0],'Gv':Gs[1],'W':W},indent=2)+'\n')
if '--full-sturm' in __import__('sys').argv:
    (ROOT/'full-sturm.json').write_text(__import__('json').dumps(chain,indent=2)+'\n')
(ROOT/'exact-basis.txt').write_text('u='+str(u)+'\nv='+str(v)+'\nalpha='+str(alpha)+'\nbeta='+str(beta)+'\ninjection='+str(n[2])+'\n')
