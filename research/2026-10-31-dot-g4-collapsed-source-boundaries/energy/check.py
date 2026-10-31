"""Exact rational scalar algebra only; no forest engine or parameter search."""
import sympy as s
import json
u=s.symbols('u'); d=s.Rational(1,4); b=u+d
r=(3*u*u-d**3)/2
k=-u**3/6+d**3*u/6+d**5/15-d**6/90
A=d**4*(1-2*d/5+d*d/15)
i=-96*k-A-8*b*r
mu=s.Rational(743,10560)
F=s.cancel(3*(6*k-2*mu*r)**2/(16*b)-mu*r*r)
P=7136870400*u**5-4797112320*u**4-212216256*u**3+47710704*u**2+1066716*u-101459
D=s.Integer(38063308800)
assert s.factor(F-P/D)==0
assert mu==3*k.subs(u,-d)/r.subs(u,-d)
m={0:s.Integer(1),1:-s.Rational(493,7680),2:s.Rational(1,192),3:-s.Rational(103,163840)}
mean=lambda expr:s.expand(sum(s.expand(expr).coeff(u,j)*m[j] for j in range(4)))
assert mean(r)==0 and mean(k)==0 and mean(i)==0
# Check that these are the unique first-three moments forced by the three sums.
x1,x2,x3=s.symbols('x1 x2 x3'); mm={0:s.Integer(1),1:x1,2:x2,3:x3}
ma=lambda expr:sum(s.expand(expr).coeff(u,j)*mm[j] for j in range(4))
sol=s.solve([ma(r),ma(k),ma(i)],(x1,x2,x3))
assert sol=={x1:m[1],x2:m[2],x3:m[3]}
C=sum(P.coeff(u,j)*m[j] for j in range(4)); m4lower=m[3]**2/m[2]
upper=s.factor((C-4797112320*m4lower)/D)
assert C==s.Rational(542646221,2560)
assert m4lower==s.Rational(31827,419430400)
assert upper==-s.Rational(12455183,3118146256896)
# Pointwise completion-of-the-square identity.
S=s.symbols('S'); expr=6*S*k-s.Rational(4,3)*b*S*S-mu*(2*S*r+r*r)
assert s.factor(F-expr-s.Rational(4,3)*b*(S-3*(6*k-2*mu*r)/(8*b))**2)==0
out={'scope':__doc__,'potential':str(mu),'exact_polynomial_identity':True,'source_moments_unique':{str(k):str(v) for k,v in sol.items()},'square_completion':True,'low_moment_numerator':str(C),'fourth_moment_lower_bound':str(m4lower),'mean_F_upper_bound':str(upper),'all_checks':True}
print(json.dumps(out,indent=2))
