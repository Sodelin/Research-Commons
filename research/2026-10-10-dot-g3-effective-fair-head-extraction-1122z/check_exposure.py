from fractions import Fraction as F
from pathlib import Path
import json
root=Path(__file__).resolve().parent
E=(0,1,3,6,10,15,21,28)
X=(F(1),F(1,2),F(1,3),F(1,6))
def solve(A,b):
 A=[[F(x) for x in r]+[F(v)] for r,v in zip(A,b)];n=len(A)
 for j in range(n):
  i=next(i for i in range(j,n) if A[i][j]);A[j],A[i]=A[i],A[j]
  t=A[j][j];A[j]=[x/t for x in A[j]]
  for i in range(n):
   if i!=j:
    t=A[i][j];A[i]=[x-t*y for x,y in zip(A[i],A[j])]
 return [A[i][-1] for i in range(n)]
A=[ [F(int(k==0)) for k in E], [F(1)]*8 ]
for x in X[1:]:A.extend([[x**k for k in E],[F(k)*x**(k-1) if k else F(0) for k in E]])
P=solve(A,[1]+[0]*7)
assert all(sum(x*y for x,y in zip(row,P))==v for row,v in zip(A,[1]+[0]*7))
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def div(a,b):
 a=a[:];out=[F(0)]*(len(a)-len(b)+1)
 while len(a)>=len(b):
  k=len(a)-len(b);t=a[-1]/b[-1];out[k]=t
  for i,y in enumerate(b):a[i+k]-=t*y
  while a and not a[-1]:a.pop()
 assert not a
 return out
f=[F(0)]*29
for k,x in zip(E,P):f[k]=x
D=[F(1),F(-1)]
for x in X[1:]:D=mul(D,mul([-x,F(1)],[-x,F(1)]))
G=div(f,D)
print('P sparse coefficients',P)
print('G degree',len(G)-1,'all coefficients positive',all(x>0 for x in G),'G0',G[0])
T=(0,1,3,6);V=[[x**k for k in T] for x in X]
Ls=[solve(V,[int(i==j) for i in range(4)]) for j in range(4)]
assert all(sum(x*y for x,y in zip(V[i],Ls[j]))==int(i==j) for i in range(4) for j in range(4))
CP=sum(abs(x) for x in P[1:]);M=sum(abs(x) for r in Ls for x in r);DD=sum(k*abs(x) for r in Ls for k,x in zip(T,r));CL=sum(abs(x) for r in Ls for k,x in zip(T,r) if k)
print('cardinal coefficients',Ls)
print('CP',CP,'M',M,'D',DD,'CL',CL)
assert G[0]==1296 and all(x>0 for x in G)
print('PASS P(x)>=(1296)*(1-x)*prod_(r=1/2,1/3,1/6)(x-r)^2 on[0,1]')
print('PASS P>=1296*rho^7 on K_rho; explicit rational minimum bound without RCF search')
(root/'exposure-certificate.json').write_text(json.dumps({'exponents':E,'P':[str(x) for x in P],'cardinal_exponents':T,'L':[[str(x) for x in r] for r in Ls],'G_ascending':[str(x) for x in G],'CP':str(CP),'M':str(M),'D':str(DD),'CL':str(CL)},indent=2)+'\n')
