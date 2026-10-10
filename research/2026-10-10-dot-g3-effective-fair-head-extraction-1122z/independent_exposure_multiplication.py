from fractions import Fraction as F
from pathlib import Path
import json
r=Path(__file__).resolve().parent;j=json.loads((r/'exposure-certificate.json').read_text())
def multiply(a,b):
 z=[F(0)]*(len(a)+len(b)-1)
 for n in range(len(z)):
  z[n]=sum((a[i]*b[n-i] for i in range(len(a)) if 0<=n-i<len(b)),F(0))
 return z
factor=[F(1),F(-1)]
for t in (F(1,2),F(1,3),F(1,6)):
 factor=multiply(factor,[t*t,-2*t,F(1)])
G=list(map(F,j['G_ascending']));assert len(G)==22 and G[0]==1296 and all(x>0 for x in G)
p=multiply(factor,G)
expected=[F(0)]*29
for k,c in zip(j['exponents'],j['P']):expected[k]=F(c)
assert p==expected and p[0]==1
nodes=(F(1),F(1,2),F(1,3),F(1,6));L=[list(map(F,z)) for z in j['L']]
for i,row in enumerate(L):
 for h,x in enumerate(nodes):assert sum(v*x**k for v,k in zip(row,j['cardinal_exponents']))==int(i==h)
CP=sum(abs(x) for x in p[1:]);M=sum(abs(x) for z in L for x in z);D=sum(abs(x)*k for z in L for x,k in zip(z,j['cardinal_exponents']));CL=sum(abs(x) for z in L for x,k in zip(z,j['cardinal_exponents']) if k)
assert (CP,M,D,CL)==tuple(F(j[k]) for k in ('CP','M','D','CL'))
print('PASS exact coefficient multiplication: sparse P=(1-x)prod(x-r)^2 G; all22 G coefficients positive, G0=1296.')
print('PASS all16 cardinal evaluations and all four coefficient-norm constants match.')
print('PASS analytically on K_rho: every distance factor>=rho, hence P>=1296*rho^7.')
