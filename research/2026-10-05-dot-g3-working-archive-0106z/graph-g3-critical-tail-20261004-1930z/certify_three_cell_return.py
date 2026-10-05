"""Exact interval contraction certificate for ONE cap-four source calibration.
Numerical root selection is separate from the rational acceptance test.
"""
from fractions import Fraction as R
from itertools import combinations
from pathlib import Path
import json, math
import mpmath as mp
import numpy as np

HERE=Path(__file__).parent
old=json.loads((HERE/'THREE-CELL-NUMERICAL-CALIBRATION.json').read_text())
v0=min(old['results'],key=lambda row:row['norm'])['parameters']

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

mp.mp.dps=110
vmp=list(map(lambda z:mp.mpf(str(z)),v0))
J=np.array(mp.matrix([[mp.diff(lambda z: defects(vmp[:j]+[z]+vmp[j+1:])[i],vmp[j]) for j in range(8)] for i in range(4)]).tolist(),float)
# Select one numerically well-conditioned square submatrix; exact verification follows.
piv=min(combinations(range(8),4),key=lambda ix:np.linalg.cond(J[:,ix]))
fixed=[R(str(x)) for x in v0]
def fill(xs):
 v=[mp.mpf(z.numerator)/z.denominator for z in fixed]
 for j,x in zip(piv,xs):v[j]=x
 return v
def fun(*xs):return tuple(defects(fill(xs)))
root=mp.findroot(fun,tuple(vmp[j] for j in piv),tol=mp.mpf('1e-100'),maxsteps=100)
cent=[R(mp.nstr(x,95)) for x in root]
centmp=[mp.mpf(x.numerator)/x.denominator for x in cent]
Jp=mp.matrix([[mp.diff(lambda z:fun(*(centmp[:j]+[z]+centmp[j+1:]))[i],centmp[j]) for j in range(4)] for i in range(4)])
Ai=Jp**-1
A=[[R(mp.nstr(Ai[i,j],80)) for j in range(4)] for i in range(4)]
rho=R(1,10**30)

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

v=[D(x) for x in fixed]
for i,j in enumerate(piv):v[j]=D(I(cent[i]-rho,cent[i]+rho),[I(int(k==i)) for k in range(4)])
Fbox=defects(v)
eta=max(sum((I(int(i==j))-sum(A[i][k]*Fbox[k].d[j] for k in range(4))).bound() for j in range(4)) for i in range(4))
vc=fixed[:]
for j,c in zip(piv,cent):vc[j]=c
fc=defects(vc)
eps=max(abs(sum(A[i][k]*fc[k] for k in range(4))) for i in range(4))
interior=all(R(0)<c-rho<c+rho<R(1) for c in cent) and all(0<x<1 for x in fixed)
assert interior and eta<R(1,2) and eps+eta*rho<rho
b2box=body(v)[0].v
assert 0<b2box.a<b2box.b<1

def rat(x):return str(x.numerator)+'/'+str(x.denominator)
cert={'status':'EXACT_RATIONAL_CONTRACTION_PASS','scope':'one actual cap-four three-cell independent source, not a global G3 theorem','pivot_indices':list(piv),'fixed_parameters':[rat(x) for x in fixed],'center':[rat(x) for x in cent],'radius':rat(rho),'preconditioner':[[rat(x) for x in row] for row in A],'eta_upper_decimal_for_display':mp.nstr(mp.mpf(eta.numerator)/eta.denominator,12),'residual_upper_decimal_for_display':mp.nstr(mp.mpf(eps.numerator)/eps.denominator,12),'exact_tests':{'box_strictly_in_unit_cube':interior,'eta_lt_half':eta<R(1,2),'invariance_eps_plus_eta_rho_lt_rho':eps+eta*rho<rho,'pair_survival_strict':0<b2box.a<b2box.b<1,'body_pair_survival_gt_one_eighth':b2box.a>R(1,8)},'body_pair_survival_interval_display':[float(b2box.a),float(b2box.b)],'verification':'Exact rational interval operations and inequalities; numerical stages only choose certificate data.'}
(HERE/'THREE-CELL-EXACT-CERTIFICATE.json').write_text(json.dumps(cert,indent=2)+'\n')
print(json.dumps({k:v for k,v in cert.items() if k not in ['preconditioner','center','fixed_parameters']},indent=2))
