"""Exact formal reference-denominator and small-H scalar cancellations."""
import sympy as s

h,T=s.symbols('h T',positive=True)
w=s.exp(-27*h)
ratio=(1-w*(1-10*h**3))/((1-4*h**3)-w*(1-20*h**3))
jet=s.series(ratio,h,0,3).removeO().expand()
assert s.simplify(jet-(1-s.Rational(2,9)*h**2))==0
A=s.exp(-T); B=s.exp(-10*T)
baseline=(-6*A+15*B)*(2*T/9)-s.Rational(2,9)*(A-B)
assert s.simplify(baseline.subs(T,0))==0
assert s.simplify(s.diff(baseline,T).subs(T,0))==0
print('PASS: equal-rate reference denominator ratio = 1-(2/9)h^2+O(h^3)')
print('PASS: endpoint leading baseline cancels through first order in T')
print('Uses only saved fair diagonal jets; no source bank or grid')
