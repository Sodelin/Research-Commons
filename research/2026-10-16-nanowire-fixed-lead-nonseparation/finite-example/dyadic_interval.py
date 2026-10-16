"""Own outward-rounded integer/dyadic intervals. No floating point acceptance."""
from fractions import Fraction as F
P=1024; Q=1<<P
class I:
 __slots__=('lo','hi')
 def __init__(self,x=0,hi=None,raw=False):
  if raw:self.lo,self.hi=x,hi
  else:
   x=F(x); h=x if hi is None else F(hi)
   self.lo=x.numerator*Q//x.denominator
   self.hi=-((-h.numerator*Q)//h.denominator)
  assert self.lo<=self.hi
 @staticmethod
 def box(lo,hi):return I(lo,hi,True)
 @staticmethod
 def of(x):return x if isinstance(x,I) else I(x)
 def __add__(a,b):
  b=I.of(b);return I.box(a.lo+b.lo,a.hi+b.hi)
 __radd__=__add__
 def __neg__(a):return I.box(-a.hi,-a.lo)
 def __sub__(a,b):return a+-I.of(b)
 def __rsub__(a,b):return I.of(b)+-a
 def __mul__(a,b):
  b=I.of(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
  return I.box(min(v)//Q,-(-max(v)//Q))
 __rmul__=__mul__
 def square(a):
  lower=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
  upper=max(a.lo*a.lo,a.hi*a.hi)
  return I.box(lower//Q,-(-upper//Q))
 def inv(a):
  assert a.lo>0 or a.hi<0, 'zero in interval divisor'
  return I.box(Q*Q//a.hi,-(-Q*Q//a.lo))
 def __truediv__(a,b):return a*I.of(b).inv()
 def __rtruediv__(a,b):return I.of(b)*a.inv()
 def lower(a):return F(a.lo,Q)
 def upper(a):return F(a.hi,Q)
 def sign(a):return 1 if a.lo>0 else -1 if a.hi<0 else 0
 def out(a):return {'lower':str(a.lower()),'upper':str(a.upper()),'decimal_lower':float(a.lower()),'decimal_upper':float(a.upper())}
class D:
 """Dual interval for one real scalar derivative."""
 __slots__=('v','d')
 def __init__(self,v=0,d=0):self.v=I.of(v);self.d=I.of(d)
 @staticmethod
 def of(x):return x if isinstance(x,D) else D(x)
 def __add__(a,b):
  b=D.of(b);return D(a.v+b.v,a.d+b.d)
 __radd__=__add__
 def __neg__(a):return D(-a.v,-a.d)
 def __sub__(a,b):return a+-D.of(b)
 def __rsub__(a,b):return D.of(b)+-a
 def __mul__(a,b):
  b=D.of(b);return D(a.v*b.v,a.d*b.v+a.v*b.d)
 __rmul__=__mul__
 def inv(a):return D(a.v.inv(),-a.d/(a.v*a.v))
 def __truediv__(a,b):return a*D.of(b).inv()
 def __rtruediv__(a,b):return D.of(b)*a.inv()
class C:
 """Complex rectangle; each coordinate is an outward-rounded interval."""
 __slots__=('r','i')
 def __init__(self,r=0,i=0):self.r=I.of(r);self.i=I.of(i)
 @staticmethod
 def of(x):return x if isinstance(x,C) else C(x)
 def __add__(a,b):
  b=C.of(b);return C(a.r+b.r,a.i+b.i)
 __radd__=__add__
 def __neg__(a):return C(-a.r,-a.i)
 def __sub__(a,b):return a+-C.of(b)
 def __rsub__(a,b):return C.of(b)+-a
 def __mul__(a,b):
  b=C.of(b);return C(a.r*b.r-a.i*b.i,a.r*b.i+a.i*b.r)
 __rmul__=__mul__
 def inv(a):
  # Squaring by interval multiplication is enclosing but can be loose near zero.
  z=a.r.square()+a.i.square()
  assert z.lo>0,'complex interval divisor not certified away from zero'
  return C(a.r/z,-a.i/z)
 def __truediv__(a,b):return a*C.of(b).inv()
 def __rtruediv__(a,b):return C.of(b)*a.inv()
def mm(a,b):return [[sum((a[i][k]*b[k][j] for k in range(len(b))),0) for j in range(len(b[0]))] for i in range(len(a))]
def sub(a,b):return [[x-y for x,y in zip(u,v)] for u,v in zip(a,b)]
def det2(a):return a[0][0]*a[1][1]-a[0][1]*a[1][0]
def inv2(a):
 d=det2(a);return [[a[1][1]/d,-a[0][1]/d],[-a[1][0]/d,a[0][0]/d]]
def inverse(a):
 n=len(a);b=[[a[i][j] for j in range(n)]+[C(int(i==j)) for j in range(n)] for i in range(n)]
 for k in range(n):
  z=b[k][k].inv();b[k]=[x*z for x in b[k]]
  for i in range(n):
   if i!=k:
    z=b[i][k];b[i]=[x-z*y for x,y in zip(b[i],b[k])]
 return [r[n:] for r in b]
def determinant(a):
 n=len(a);b=[row[:] for row in a];d=C(1)
 for k in range(n):
  z=b[k][k];d=d*z
  if k<n-1:
   zi=z.inv()
   for i in range(k+1,n):
    q=b[i][k]*zi
    for j in range(k+1,n):b[i][j]=b[i][j]-q*b[k][j]
 return d
