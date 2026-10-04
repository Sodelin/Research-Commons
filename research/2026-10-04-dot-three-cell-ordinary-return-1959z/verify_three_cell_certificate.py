"""Standalone exact rational verification; no numerical root finder is used.
Verifies the supplied contraction box for the exact source polynomials.
"""
from fractions import Fraction as R
from pathlib import Path
import json, math, hashlib
HERE=Path(__file__).parent
def body(v):
 def B(x,y):
  b=[sum(math.comb(k,r)*x**(r*(r-1)//2)*y**((k-r)*(k-r-1)//2) for r in range(k+1))/2**k for k in (2,3,4)]
  a=(1-x)/2;c=(1-y)/2
  return b+[(a**3+c**3)/3-(a-c)**2/2,0]
 def E(z):return [z,z**3,z**6,0,0]
 def mul(K,L):return [K[0]*L[0],K[1]*L[1],K[2]*L[2],L[0]*K[3]+K[2]*L[3],K[4]+(1-L[0])*K[3]+K[2]*L[4]]
 return mul(mul(mul(mul(B(*v[:2]),E(v[6])),B(*v[2:4])),E(v[7])),B(*v[4:6]))
def defects(v):
 a,b,c,C,H=body(v)
 return [b-a**3,c-a**6,C,H]

class I:
 def __init__(self,a,b=None):
  if isinstance(a,I):self.a,self.b=a.a,a.b
  else:self.a=R(a);self.b=R(a if b is None else b)
 def __add__(self,o):o=I(o);return I(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a)
 def __sub__(self,o):return self+-I(o)
 def __rsub__(self,o):return I(o)+-self
 def __mul__(self,o):
  o=I(o);vs=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b];return I(min(vs),max(vs))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=I(o);assert not o.a<=0<=o.b;return self*I(1/o.b,1/o.a)
 def __pow__(self,n):
  assert isinstance(n,int) and n>=0
  out=I(1)
  for _ in range(n):out=out*self
  return out
 def bound(self):return max(abs(self.a),abs(self.b))
class D:
 def __init__(self,v,d=None):self.v=I(v);self.d=[I(0)]*4 if d is None else d
 def __add__(self,o):o=lift(o);return D(self.v+o.v,[a+b for a,b in zip(self.d,o.d)])
 __radd__=__add__
 def __neg__(self):return D(-self.v,[-x for x in self.d])
 def __sub__(self,o):return self+-lift(o)
 def __rsub__(self,o):return lift(o)+-self
 def __mul__(self,o):o=lift(o);return D(self.v*o.v,[a*o.v+self.v*b for a,b in zip(self.d,o.d)])
 __rmul__=__mul__
 def __truediv__(self,o):
  assert not isinstance(o,D);return D(self.v/o,[a/o for a in self.d])
 def __pow__(self,n):
  assert isinstance(n,int) and n>=0
  if n==0:return D(1)
  return D(self.v**n,[n*self.v**(n-1)*x for x in self.d])
def lift(o):return o if isinstance(o,D) else D(o)

cert_path=HERE/'THREE-CELL-EXACT-CERTIFICATE.json'
cert=json.loads(cert_path.read_text())
piv=cert['pivot_indices'];fixed=[R(x) for x in cert['fixed_parameters']]
cent=[R(x) for x in cert['center']];rho=R(cert['radius'])
A=[[R(x) for x in row] for row in cert['preconditioner']]
assert len(piv)==4 and len(set(piv))==4 and all(0<=j<8 for j in piv)
assert len(fixed)==8 and len(cent)==4 and len(A)==4 and all(len(row)==4 for row in A)
assert rho>0
v=[D(x) for x in fixed]
for i,j in enumerate(piv):v[j]=D(I(cent[i]-rho,cent[i]+rho),[I(int(k==i)) for k in range(4)])
Fbox=defects(v)
eta=max(sum((I(int(i==j))-sum(A[i][k]*Fbox[k].d[j] for k in range(4))).bound() for j in range(4)) for i in range(4))
vc=fixed[:]
for j,c in zip(piv,cent):vc[j]=c
fc=defects(vc)
eps=max(abs(sum(A[i][k]*fc[k] for k in range(4))) for i in range(4))
b2box=body(v)[0].v
checks={'all_parameters_strict':all(0<c-rho<c+rho<1 for c in cent) and all(0<x<1 for x in fixed),
        'derivative_contraction':eta<R(1,2),
        'box_invariance':eps+eta*rho<rho,
        'body_pair_between_one_eighth_and_one':R(1,8)<b2box.a<b2box.b<1}
assert all(checks.values()),checks
receipt={'status':'PASS','arithmetic':'exact rational interval arithmetic; no tolerance in acceptance',
         'certificate_sha256':hashlib.sha256(cert_path.read_bytes()).hexdigest(),
         'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'checks':checks,'eta_display':float(eta),'eps_display':float(eps),'radius_display':float(rho),
         'conclusion_scope':'existence of a strictly interior isolated real solution of the four cap-four source defects; no master recognizer or Lean claim'}
(HERE/'THREE-CELL-EXACT-VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
