"""Scalar matched-channel kernel and four-node interpolation algebra."""
import sympy as s

a,b,T=s.symbols('a b T', nonnegative=True)
f=a*s.exp(-9*a)
g=-s.exp(-5*a)/20+s.exp(-7*a)/3+s.exp(-9*a)/4-8*s.exp(-10*a)/15
res=s.series(f-g,a,0,5).removeO().expand()
assert s.simplify(res-a**4/3)==0
inner=s.integrate(4*s.exp(-9*a)+10*s.exp(-9*b),(a,0,b))
inner+=s.integrate(4*s.exp(-9*b)+10*s.exp(-9*a),(a,b,T))
closed=s.Rational(4,9)-s.Rational(10,9)*s.exp(-9*T)
closed+=(s.Rational(2,3)+4*T+6*b)*s.exp(-9*b)
assert s.simplify(inner-closed)==0
A=(-6*s.exp(-T)+15*s.exp(-10*T))/27
B=-s.Rational(2,243)*(s.exp(-T)-s.exp(-10*T))
cross=s.simplify(A+s.Rational(9,4)*s.exp(-T)*s.Rational(2,9)*inner)
assert s.simplify(cross-s.exp(-T)*(s.Rational(1,3)+2*T+3*b)*s.exp(-9*b))==0
q0=s.Rational(4,81)*s.integrate(inner,(b,0,T))
assert s.simplify(A*(2*T/9)+B+s.Rational(9,8)*s.exp(-T)*q0)==0
print('PASS: four-rate interpolation remainder starts a^4/3')
print('PASS: symmetric kernel inner integral, reference baseline, cross term')
print('Scalar algebra only; no forest bank or parameter grid')
