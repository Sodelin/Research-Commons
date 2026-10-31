"""Formal scalar expansion of the retained two endpoints; no source bank."""
import sympy as s

h,T,X,g1,g2=s.symbols('h T X g1 g2')
A=s.exp(-T); B=s.exp(-10*T)
k2=A
k4=s.exp(-6*T)*(1-6*X*h**2)
k5=B*(1-15*X*h**2)
k6=s.exp(-15*T)*(1-30*X*h**2)
Gamma5=h**2*(1+g1*h+g2*h**2)/27
Gamma6=Gamma5*(1-s.Rational(2,9)*h**2)
delta=s.expand(s.exp(5*T)*Gamma6*(k4-k6)-Gamma5*(k2-k5))
expected=(((-6*A+15*B)*X)-s.Rational(2,9)*(A-B))/27
assert s.simplify(delta.coeff(h,2))==0
assert s.simplify(delta.coeff(h,3))==0
assert s.simplify(delta.coeff(h,4)-expected)==0
reference=-s.Rational(2,243)*((1+6*T)*A-(1+15*T)*B)
assert s.simplify(expected.subs(X,2*T/9)-reference)==0
print('PASS: order-h^2 and h^3 endpoint differences cancel')
print('PASS: order-h^4 coefficient and fair-reference limit')
print('Formal scalar expansion only; no forest bank or parameter grid')
