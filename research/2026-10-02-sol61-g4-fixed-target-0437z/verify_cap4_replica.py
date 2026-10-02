#!/usr/bin/env python3
"""Pure exact rational replay of the G4 cap-four ordinary-target replica.
Contributor: GPT-6.1 Sol / advance_general_g3_g4, 2026-10-02.
The input center is an exact rational proposal, never an assumed exact root.
Every polynomial, derivative enclosure and fixed-point inequality is recomputed.
"""
from fractions import Fraction as Q
from math import comb
import sympy as S
import json,hashlib,time,sys
from pathlib import Path
sys.set_int_max_str_digits(0)
certificate=json.loads(Path(__file__).with_name('ordinary-cap4-certificate.json').read_text())
cols=(2,4,6,8)
names='x1 y1 g1 z1 x2 y2 g2 z2 x3 y3 g3 z3'.split()
approx=[.36859070850617354,.7248930587056989,.45829976418003954,.7557721190367547,.31662066004399286,.43664884030679246,.2984033761522679,.8633112414175388,.6731725280520244,.9121098382163854,.7452491177891054,.44300266886138906]
fixed={i:Q(round(approx[i]*10**8),10**8) for i in range(12) if i not in cols}

def cell(x,y,g):
 h=1-g
 v=[sum(comb(n,j)*g**j*h**(n-j)*x**(j*(j-1)//2)*y**((n-j)*(n-j-1)//2) for j in range(n+1)) for n in (2,3,4)]
 A=g*(1-x);B=h*(1-y)
 c=Q(2,3)*(h*A**3+g*B**3-3*g*h*(A-B)**2)
 return v+[c,0]
# Independently connect the compact C polynomial to the genuine bare forest law.
# One output root is possible only when all four roots route to one arm.
u,v,w=S.symbols('u v w')
hh=1-w
b2,b3,b4,Ccompact,Hcompact=cell(u,v,w)
P1=w**4*(1-S.Rational(9,5)*u+u**3-S.Rational(1,5)*u**6)+hh**4*(1-S.Rational(9,5)*v+v**3-S.Rational(1,5)*v**6)
Csource=S.Rational(10,3)*(P1-(1-S.Rational(9,5)*b2+b3-b4/5))
assert S.expand(Csource-Ccompact)==0
assert Hcompact==0

def comp(K,L):
 q,r,s,c,h=K;Q_,R,T,C,H=L
 return [q*Q_,r*R,s*T,Q_*c+s*C,h+(1-Q_)*c+s*H]
def kernel(p):
 K=[1,1,1,0,0]
 for i in range(3):
  K=comp(K,cell(*p[4*i:4*i+3]));z=p[4*i+3];K=comp(K,[z,z**3,z**6,0,0])
 return K
def equations(p):
 q,r,s,c,h=kernel(p)
 return [1000*(r-q**3),10**6*(s-q**6),10**6*c,10**6*h]
center=[Q(v) for v in certificate['center']]
print('Pure rational replay: loaded exact center encodings',flush=True)

class I:
 def __init__(self,a,b=None):self.a=Q(a);self.b=Q(a if b is None else b)
 def __add__(self,o):
  if not isinstance(o,I):o=I(o)
  return I(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a)
 def __sub__(self,o):return self+(-o if isinstance(o,I) else -I(o))
 def __rsub__(self,o):return I(o)+-self
 def __mul__(self,o):
  if not isinstance(o,I):o=I(o)
  p=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b];return I(min(p),max(p))
 __rmul__=__mul__
 def __pow__(self,n):
  assert n>=0
  if n==0:return I(1)
  if n%2==0 and self.a<=0<=self.b:return I(0,max(abs(self.a),abs(self.b))**n)
  p=[self.a**n,self.b**n];return I(min(p),max(p))
 def abs(self):return max(abs(self.a),abs(self.b))
 def obj(self):
  den=10**60
  lo=self.a.numerator*den//self.a.denominator
  hi=-((-self.b.numerator*den)//self.b.denominator)
  return [str(Q(lo,den)),str(Q(hi,den))]
class D:
 def __init__(self,v,d=None):self.v=v if isinstance(v,I) else I(v);self.d=[I(0)]*4 if d is None else d
 def __add__(self,o):
  if not isinstance(o,D):o=D(o)
  return D(self.v+o.v,[a+b for a,b in zip(self.d,o.d)])
 __radd__=__add__
 def __neg__(self):return D(-self.v,[-a for a in self.d])
 def __sub__(self,o):return self+(-o if isinstance(o,D) else -D(o))
 def __rsub__(self,o):return D(o)+-self
 def __mul__(self,o):
  if not isinstance(o,D):o=D(o)
  return D(self.v*o.v,[a*o.v+self.v*b for a,b in zip(self.d,o.d)])
 __rmul__=__mul__
 def __pow__(self,n):
  if n==0:return D(1)
  return D(self.v**n,[n*self.v**(n-1)*a for a in self.d])

def source_parameters(center,radius):
 p=[]
 for i in range(12):
  if i in fixed:p.append(D(fixed[i]))
  else:
   j=cols.index(i);v=I(center[j]-radius,center[j]+radius)
   p.append(D(v,[I(int(k==j)) for k in range(4)]))
 return p

# Center values and Jacobian are exact rationals, without expanded-polynomial heuristics.
point=source_parameters(center,Q(0));Fpoint=equations(point)
F0=S.Matrix([f.v.a for f in Fpoint]);J0=S.Matrix([[d.a for d in f.d] for f in Fpoint]);assert J0.det()!=0
R=J0.inv();radius=Q(1,10**25)
box=[I(t-radius,t+radius) for t in center]
P=source_parameters(center,radius)
assert all(0<p.v.a<=p.v.b<1 for p in P)
FI=equations(P);JI=[f.d for f in FI]
def rat(a):return Q(int(S.numer(a)),int(S.denom(a)))
E=[[I(int(i==j))-sum((rat(R[i,k])*JI[k][j] for k in range(4)),I(0)) for j in range(4)] for i in range(4)]
newton=[center[i]-rat((R*F0)[i]) for i in range(4)]
Kraw=[I(newton[i])+sum((E[i][j]*I(-radius,radius) for j in range(4)),I(0)) for i in range(4)]
assert all(box[i].a<Kraw[i].a and Kraw[i].b<box[i].b for i in range(4))
contraction=max(sum(e.abs() for e in row) for row in E)
assert contraction<1
assert all(0<b.a<=b.b<1 for b in box)
qbox=kernel(P)[0].v
assert qbox.a>Q(1,10) and qbox.b<1
b5=D(1)
for i in range(3):
 x,y,g,z=P[4*i:4*i+4];h=1-g
 b5*=z**10*sum(comb(5,j)*g**j*h**(5-j)*x**(j*(j-1)//2)*y**((5-j)*(5-j-1)//2) for j in range(6))
fifth_box=(b5-kernel(P)[0]**10).v
assert fifth_box.a>0 or fifth_box.b<0
rec={'status':'PASS','method':'exact rational factored-polynomial automatic differentiation and Brouwer/Krawczyk contraction','variables':[names[i] for i in cols],'fixed':{names[i]:str(t) for i,t in fixed.items()},'center':[str(a) for a in center],'radius':str(radius),'box':[x.obj() for x in box],'Krawczyk':[x.obj() for x in Kraw],'max_row_sum_bound':str(Q(-((-contraction.numerator*10**60)//contraction.denominator),10**60)),'q_box':qbox.obj(),'ordinary_target':'1/10','leading_pad':'(1/10)/q','fifth_unscaled_difference_box':fifth_box.obj(),'J0_determinant_nonzero':True,'J0_determinant_sha256':hashlib.sha256(str(J0.det()).encode()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'bare_C_source_polynomial_identity':'PASS','claims':['unique real-algebraic root in box of four original polynomial quotient equations','strict positive independent three-bigon source has every complete forest through four equal to E(1/10)','fifth no-merger response differs from E(1/10) after adding strict leading pad']}
Path('ordinary-cap4-replay.json').write_text(json.dumps(rec,indent=2,sort_keys=True))
print('PASS', 'q=',float(qbox.a),float(qbox.b),'fifth=',float(fifth_box.a),float(fifth_box.b),'contraction=',float(contraction),flush=True)
