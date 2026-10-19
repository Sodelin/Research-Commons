import sympy as s
from fractions import Fraction as F
from math import comb
z=s.symbols('z')
def cell(p,x,y):
 b=lambda n:s.expand(sum(s.binomial(n,j)*p**j*(1-p)**(n-j)*x**comb(j,2)*y**comb(n-j,2) for j in range(n+1)))
 f=lambda t:1-s.Rational(3,2)*t+t**3/2
 c=s.expand((4*p**3*(1-p)*f(x)+4*p*(1-p)**3*f(y)-12*p*p*(1-p)**2*(1-x)*(1-y))/10)
 return b(2),b(3),b(4),c
# Rational interval range of a polynomial on a positive rational interval.
def bound(poly,lo,hi):
 L=U=s.Rational(0)
 for (k,),a in s.Poly(poly,z).terms():
  v,w=lo**k,hi**k
  L+=a*(v if a>=0 else w);U+=a*(w if a>=0 else v)
 return L,U
A=cell(s.Rational(1,2),s.Rational(1,2),s.Rational(1,2))
for name,B,lo,hi,sgn in [
 ('negative',cell(s.Rational(1,10),z,z),s.Rational(34742376,10**9),s.Rational(34742378,10**9),-1),
 ('positive',cell(s.Rational(1,100),s.Rational(1,1000),z),s.Rational(450415756,10**9),s.Rational(450415760,10**9),1)]:
 P=s.expand(A[1]*B[1]-(A[0]*B[0])**3)
 D=s.expand(A[2]*B[2]-(A[0]*B[0])**6)
 assert P.subs(z,lo)*P.subs(z,hi)<0
 dP=bound(s.diff(P,z),lo,hi); assert dP[0]*dP[1]>0
 assert bound(A[0]*B[0],lo,hi)[0]>s.Rational(1,100)
 d=bound(D,lo,hi); assert (d[0]>0 if sgn>0 else d[1]<0)
 print(name,'P=',s.factor(P),'root interval',lo,hi,'D4 sign',sgn)
 if name=='negative':
  # A4(A E(t) B)=cA/b2A + (b4A/b2A) exp(-5t) cB/b2B.
  # exp(-5t)= -cA*b2B/(b4A*cB). Positivity and <1 certified polynomially.
  num=-A[3]*B[0];den=A[2]*B[3]
  assert bound(num,lo,hi)[0]>0 and bound(den,lo,hi)[0]>0
  assert bound(den-num,lo,hi)[0]>0
  assert bound(num-den/100,lo,hi)[0]>0
  print('positive connector t exists: exp(-5t)=',s.factor(num/den),'strictly between 0 and 1')
print('PASS: exact algebraic roots, opposite four-root diagonal signs at exact three-root matching, and chronological c4 cancellation with positive gap')
