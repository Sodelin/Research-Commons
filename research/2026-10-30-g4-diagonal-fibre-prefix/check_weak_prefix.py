import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from check_defect import defect
from fractions import Fraction as F
import sympy as s
import json
x,g=s.symbols('x g',real=True)
f4=s.factor(defect(4,1-5*x,1-x,g));f5=s.factor(defect(5,1-5*x,1-x,g))
Q=(126*x-108)*g*g+(36-2*x)*g+x-3
assert s.expand(f4+F(2,3)*x*x*g*(1-g)*Q)==0
rem=s.factor(s.rem(f5,Q,g))
# Rational analytic remainder suffices for the leading asymptotic; no numerical fit.
assert s.simplify(s.limit(rem/x**4,x,0)-s.Rational(625,27)*(g-s.Rational(1,6)))==0
u=s.symbols('u',positive=True)
roots=[(18-x+sgn*5*s.sqrt(x*(18-5*x)))/(108-126*x) for sgn in [-1,1]]
limits=[]
for sgn,root in zip([-1,1],roots):
 assert s.simplify(Q.subs(g,root))==0
 rootu=root.subs(x,u*u)
 first=s.limit((rootu-s.Rational(1,6))/u,u,0,dir='+')
 assert s.simplify(first-sgn*5*s.sqrt(2)/36)==0
 leading=s.simplify(s.Rational(625,27)*first)
 assert s.simplify(leading-sgn*3125*s.sqrt(2)/972)==0
 limits.append(str(leading))
fair=s.factor(defect(4,1-x,1-x,F(1,2)))
bias=s.factor(defect(4,1-x,1-x,F(1,10)))
assert fair==-x**3/12
assert s.expand(bias-3*x*x*(96-41*x)/2500)==0
print(json.dumps(dict(status='PASS',zero_polynomial=str(Q),dev4=str(f4),dev5_remainder=str(rem),roots=list(map(str,roots)),limit_dev5_over_x9half=limits,fair_prefix_dev4=str(fair),biased_prefix_dev4=str(bias),scope='Exact symbolic weak-cell checks only; fibre insertion uses inherited full-rank theorem and hand IFT, not an executed all-cap word construction'),indent=2))
