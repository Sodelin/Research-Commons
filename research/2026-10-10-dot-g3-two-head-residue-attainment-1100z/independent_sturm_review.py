from fractions import Fraction as F
from pathlib import Path
import json
root=Path(__file__).resolve().parent
# First run: python check_exact.py --full-sturm
j=json.loads((root/'exact-polynomials.json').read_text()); C=json.loads((root/'full-sturm.json').read_text())
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def rem(a,b):
 a=list(map(F,a))
 while len(a)>=len(b) and a!=[0]:
  s=len(a)-len(b);c=a[-1]/b[-1]
  for i,x in enumerate(b):a[i+s]-=c*x
  trim(a)
 return a
def prop(a,b,sign):
 assert len(a)==len(b)
 scale=a[-1]/F(b[-1]);assert sign*scale>0
 assert all(x==scale*y for x,y in zip(a,b))
assert C[0]==j['W']
prop([i*C[0][i] for i in range(1,len(C[0]))],C[1],1)
for a,b,c in zip(C,C[1:],C[2:]):prop(rem(a,b),c,-1)
assert len(C[-1])==1 and C[-1][0]!=0
print('PASS: every supplied Sturm step independently checked by ordinary Fraction polynomial long division; negative remainder is a positive multiple of next row.')
def ev(a,x):
 out=F(0)
 for v in reversed(a):out=out*x+v
 return out
def var(x):
 vals=[ev(a,x) for a in C];assert vals[0]!=0
 signs=[1 if z>0 else -1 for z in vals if z]
 return sum(x!=y for x,y in zip(signs,signs[1:]))
I=[(F(121,500),F(61,250)),(F(37,125),F(149,500)),(F(223,500),F(56,125)),(F(501,1000),F(503,1000))]
assert var(F(0))-var(F(1))==4
assert all(var(a)-var(b)==1 for a,b in I)
assert all(b*b<c or d<a*a for a,b in I for c,d in I)
print('PASS: total four roots, one in each interval, and no square-related root pair.')
