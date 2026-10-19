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
A=cell(s.Rational(22,100),s.Rational(69,100),s.Rational(94,100))
B=cell(s.Rational(32,100),s.Rational(21,100),z)
lo=s.Rational(84189351532,10**11);hi=s.Rational(84189351534,10**11)
P=s.expand(A[1]*B[1]-(A[0]*B[0])**3)
D=s.expand(A[2]*B[2]-(A[0]*B[0])**6)
assert P.subs(z,lo)*P.subs(z,hi)<0
L,U=bound(s.diff(P,z),lo,hi);assert L*U>0
assert bound(D,lo,hi)[0]>0
# Here cA is negative and cB positive; choose positive denominator signs.
assert A[3]<0 and bound(B[3],lo,hi)[0]>0
num=-A[3]*B[0];den=A[2]*B[3]
assert bound(num,lo,hi)[0]>0 and bound(den-num,lo,hi)[0]>0
assert bound(num-den/100,lo,hi)[0]>0
assert bound(A[0]*B[0],lo,hi)[0]>s.Rational(1,100)
print('A=(11/50,69/100,47/50); B=(8/25,21/100,z)')
print('root interval',lo,hi)
print('P=',s.factor(P))
print('D4 strictly positive; cA negative, cB positive; connector ratio strictly between 1/100 and 1')
print('PASS exact three-root equality and positive-fourth-diagonal example with zero chronological c4 and positive h=10 padding')
