import sympy as s
from itertools import product
m,n,r,d=s.symbols('m n r d', real=True)
e1=e2=0
for x1,x2,y in product([-1,1],repeat=3):
 p=(1+m*x1)*(1+m*x2)*(1+n*y)/8
 z=s.Rational(1)*x1*x2-s.Rational(1,2)*y*(x1+x2)
 e1+=p*z; e2+=p*z*z
assert s.expand(e1-(m*m-m*n))==0
assert s.expand(e2-(s.Rational(3,2)+m*m/2-2*m*n))==0
for direction in [-1,1]:
 av1=av2=0
 for sig in [-1,1]:
  subs={m:r+direction*2*sig*d,n:r-direction*2*sig*d}
  av1+=e1.subs(subs)/2; av2+=e2.subs(subs)/2
 assert s.expand(av1-8*d*d)==0
 assert s.expand(av2-(s.Rational(3,2)*(1-r*r)+10*d*d))==0
assert 4*15*27**2==43740
for k in [5,6,7]:
 exponent=s.Rational(11,3)-s.Rational(2,3)*(k-1)
 assert exponent==s.Rational(13-2*k,3)
print('PASS: full eight-outcome contrast moments; both majority-source orientations.')
print('PASS: symmetric signal moments, Chebyshev constant43740, exponent formula.')
print('Only bounded exact algebra controls; no simulation or full theorem by enumeration.')
