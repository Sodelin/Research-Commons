#!/usr/bin/env python3
"""Bounded symbolic identities; not a full source theorem or radius execution."""
import sympy as s
t,u,v,w,zeta,ya=s.symbols('t u v w zeta ya', real=True)
r=s.symbols('r', positive=True)
n=s.symbols('n', integer=True, positive=True)
def tr(e):
    return s.series(e,t,0,4).removeO().expand()
zp=t+t**3*u; qp=r+t**2*v
zs=t**2*(s.Rational(1,2)+t*w); qs=r**2+t*zeta
primary=tr(s.log(1+zp)-s.log(1+zp*qp**n))
secondary=tr(s.log(1+zs)-s.log(1+zs*qs**n))
expected_primary=t*(1-r**n)-t**2*(1-r**(2*n))/2+t**3*(u*(1-r**n)-v*n*r**(n-1)+(1-r**(3*n))/3)
expected_secondary=t**2*(1-r**(2*n))/2+t**3*(w*(1-r**(2*n))-zeta*n*r**(2*n-2)/2)
assert s.simplify(primary-expected_primary)==0
assert s.simplify(secondary-expected_secondary)==0
assert s.expand(primary+secondary-t*(1-r**n)).coeff(t,2)==0
assert tr(s.log(1+t**3*ya))==t**3*ya
assert tr(s.log(1+t**4))==0
x=s.symbols('x')
assert s.integrate(x*(1-x)**2/2,(x,0,1))==s.Rational(1,24)
print('PASS primary scaled odds/node series for symbolic positive integer exponent')
print('PASS secondary series and exact second-order cancellation')
print('PASS active baseline t^3 and inactive positive-baseline insertion t^4')
print('PASS Taylor-integral derivative factor 1/24')
print('No analytic/source theorem, contraction constants, RCF solve or witness executed.')
