from fractions import Fraction as F
import sympy as s
import json
from check_defect import defect
from check_sampling import mass

g=s.symbols('g');a=F(1,10);b=F(1,2)
f4=s.factor(defect(4,a,b,g));f5=s.factor(defect(5,a,b,g));Q=5026*g*g-3950*g+625
assert s.expand(f4+g*(g-1)*Q/1500)==0
assert s.expand(f5-g*(g-1)*(4435624*g**3-7864375*g*g+3734375*g-453125)/1000000)==0
# A second coefficient implementation using all block assignments.
for n,f in [(4,f4),(5,f5)]:
 ff=F(n-3,n-1)*mass(n,[3],a,b,g)-F(2,n-1)*mass(n,[2,2],a,b,g)
 assert s.expand(f-ff)==0
rem=s.rem(f5,Q,g)
threshold=F(3404651431,10457548744)
assert s.expand(rem-s.Rational(71470809697275,1276203503953952)*(g-s.Rational(threshold.numerator,threshold.denominator)))==0
# Q has exactly two roots, one in each interval by signs and degree2.
assert Q.subs(g,s.Rational(1,5))>0 and Q.subs(g,s.Rational(1,4))<0
assert Q.subs(g,s.Rational(1,2))<0 and Q.subs(g,s.Rational(3,5))>0
assert F(1,4)<threshold<F(1,2)
roots=[(1975-225*s.sqrt(15))/5026,(1975+225*s.sqrt(15))/5026]
assert all(s.simplify(Q.subs(g,r))==0 for r in roots)
print(json.dumps(dict(status='PASS',a=str(a),b=str(b),polynomial_dev4=str(f4),polynomial_dev5=str(f5),dev5_remainder=str(rem),roots=list(map(str,roots)),root_intervals=['(1/5,1/4)','(1/2,3/5)'],sign_threshold=str(threshold),exact_next_signs=['negative','positive'],checks='exact symbolic identities, independent block-assignment formulas, rational root isolation; no approximate root is evidence'),indent=2))
