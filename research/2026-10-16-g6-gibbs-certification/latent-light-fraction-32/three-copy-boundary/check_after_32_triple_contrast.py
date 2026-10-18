"""Exact symbolic controls for the after32 route assessment, 2026-10-18.

These verify finite-outcome identities and scalar accounting, not the full
asymptotic Bayes/physical theorem by execution.
"""
import itertools
import sympy as sp

m, n, r, d, theta = sp.symbols("m n r d theta", real=True)
moments = [sp.Integer(0), sp.Integer(0)]
for x1, x2, y in itertools.product((-1, 1), repeat=3):
    p = (1 + m*x1)*(1 + m*x2)*(1 + n*y)/8
    z = x1*x2 - sp.Rational(1, 2)*y*(x1+x2)
    assert -1 <= z <= 2
    assert z == (-x1)*(-x2) - sp.Rational(1, 2)*(-y)*(-x1-x2)
    moments[0] += p*z
    moments[1] += p*z*z
assert sp.simplify(moments[0] - (m*m-m*n)) == 0
assert sp.simplify(moments[1] - (sp.Rational(3,2)+m*m/2-2*m*n)) == 0
assert sp.simplify(moments[0].subs(n,m)) == 0
assert sp.simplify(moments[1].subs(n,m) - sp.Rational(3,2)*(1-m*m)) == 0
for orientation in (-1, 1):
    averaged = [sum(expr.subs({m:r+orientation*2*sgn*d,n:r-orientation*2*sgn*d}) for sgn in (-1,1))/2 for expr in moments]
    assert sp.simplify(averaged[0]-8*d*d) == 0
    assert sp.simplify(averaged[1] - sp.Rational(3,2)*(1-r*r)-10*d*d) == 0

f = 30*theta**2*(1-theta)**2
assert sp.integrate(theta*f,(theta,0,1)) == sp.Rational(1,2)
assert sp.integrate(theta**2*f,(theta,0,1)) == sp.Rational(2,7)
s, alpha, D, mu, a, gamma, k = sp.symbols("s alpha D mu a gamma k", positive=True)
M0 = a**3*D*mu**3*alpha**2/(27*s)
variance = 15*a**3*D*mu*s
assert sp.simplify(4*variance/M0**2 - 43740*s**3/(a**3*D*mu**5*alpha**4)) == 0
assert sp.simplify(16*s**2*(alpha/s)**4/(sp.Rational(3,2)*s) - sp.Rational(32,3)*alpha**4/s**3) == 0
mu_two = gamma*(s**4/(alpha**4*D))**sp.Rational(1,3)
assert sp.simplify(D*mu_two**5*alpha**4/s**3 - gamma**5*alpha**(-sp.Rational(8,3))*s**sp.Rational(11,3)*D**(-sp.Rational(2,3))) == 0
assert sp.expand(sp.Rational(11,3)-sp.Rational(2,3)*(k-1)) == (13-2*k)/3
assert sp.Rational(1,32)/25 == sp.Rational(1,800)

print("PASS: all eight spin outcomes, exact first/second moments and common-flip invariance")
print("PASS: both majority-source allocations after symmetric perturbation averaging")
print("PASS: Beta moments, Chebyshev constant, divergence scale and physical hybrid constant")
print("Scope: exact symbolic controls; no all-size statistical or physical execution claim")
