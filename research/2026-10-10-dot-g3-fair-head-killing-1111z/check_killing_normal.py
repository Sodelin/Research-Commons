from fractions import Fraction as F
from math import gcd,lcm
from functools import reduce
from pathlib import Path
import json
root=Path(__file__).resolve().parent
L=(1,3,6,10,15,21,28)
M=[[F(k) for k in L],[F(1)]*7]
for q in (F(1,2),F(1,3)):
 z=[q**k for k in L]
 M += [[2*(1-v)/(1+v) for v in z],[k*v/(1+v) for k,v in zip(L,z)]]
A=[r[:] for r in M];piv=[];row=0
for col in range(7):
 i=next((i for i in range(row,6) if A[i][col]),None)
 if i is None:continue
 A[row],A[i]=A[i],A[row];z=A[row][col];A[row]=[x/z for x in A[row]]
 for i in range(6):
  if i!=row:
   z=A[i][col];A[i]=[x-z*y for x,y in zip(A[i],A[row])]
 piv.append(col);row+=1
 if row==6:break
assert piv==list(range(6))
c=[-A[i][6] for i in range(6)]+[F(1)]
den=reduce(lcm,(x.denominator for x in c),1);c=[int(x*den) for x in c]
g=reduce(gcd,(abs(x) for x in c));c=[x//g for x in c]
if c[0]>0:c=[-x for x in c]
assert all(sum(x*y for x,y in zip(r,c))==0 for r in M)
print('PASS rank six; unique primitive normal c=',c)
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def prim(a):
 a=trim(a[:]);g=reduce(gcd,(abs(x) for x in a),0)
 return [x//g for x in a] if g else [0]
def divrem(a,b):
 a=list(map(F,a));out=[F(0)]*max(1,len(a)-len(b)+1)
 while len(a)>=len(b) and a!=[0]:
  k=len(a)-len(b);t=a[-1]/b[-1];out[k]+=t
  for i,y in enumerate(b):a[k+i]-=t*y
  trim(a)
 return out,a
def toints(a):
 d=reduce(lcm,(x.denominator for x in a),1)
 return prim([int(x*d) for x in a])
f=[F(0)]*29;f[0]=sum(c)
for k,x in zip(L,c):f[k]-=x
Q,rem=divrem(f,[0,1,-2,1]);assert rem==[0]
assert all(x.denominator==1 for x in Q)
Q=[int(x) for x in Q];assert len(Q)==26
# Ordinary rational long division; only positive gcd/denominator rescaling.
C=[prim(Q),prim([i*Q[i] for i in range(1,len(Q))])]
while len(C[-1])>1:
 _,r=divrem(C[-2],C[-1]);assert r!=[0]
 C.append(toints([-x for x in r]))
def ev(a,x):
 out=F(0)
 for v in reversed(a):out=out*x+v
 return out
def var(x):
 vs=[ev(a,x) for a in C];assert vs[0]!=0
 s=[1 if v>0 else -1 for v in vs if v]
 return sum(x!=y for x,y in zip(s,s[1:]))
assert ev(Q,F(0))>0 and ev(Q,F(1))>0
assert var(F(0))==var(F(1))
assert ev(Q,F(1))==F(-sum(x*k*k for x,k in zip(c,L)),2)
print('PASS F_c(z)=z(1-z)^2 Q(z), degree Q=25')
print('Q(0)=',Q[0]);print('Q(1)=',sum(Q))
print('Sturm chain degrees',[len(x)-1 for x in C])
print('Sturm variations at0,1:',var(F(0)),var(F(1)))
print('PASS Q strictly positive on [0,1]; no zero including endpoints')
(root/'killing-normal-certificate.json').write_text(json.dumps({'Lambda':L,'normal':c,'Q_ascending':Q,'Sturm_chain':C},indent=2)+'\n')
