"""Exact fair-source fourth diagonal coefficient and uniform remainder support."""
import sympy as s
a,b,t=s.symbols('a b t');z=s.symbols('z')
q2=(1+s.exp(-a*t)*s.cosh(b*t))/2
q3=(s.exp(-3*a*t)*s.cosh(3*b*t)+3*s.exp(-a*t)*s.cosh(b*t))/4
q4=(s.exp(-6*a*t)*s.cosh(6*b*t)+4*s.exp(-3*a*t)*s.cosh(3*b*t)+3*s.exp(-2*a*t))/8
K4=s.series(s.log(q4)-4*s.log(q3)+6*s.log(q2),t,0,5).removeO().expand()
print('K4 physical total-degree <=4:',K4,flush=True)
assert s.expand(K4-(-3*a*b*b*t**3/2+3*a**4*t**4/16+15*a*a*b*b*t**4/4-3*b**4*t**4/4))==0
print('PASS exact leading 3a4/16-3az/2, remainder O(a5+a²z+z²) by analyticity/evenness.',flush=True)
print('No numerical search or source return claimed.',flush=True)
