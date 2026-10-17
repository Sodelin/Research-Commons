"""Exact symbolic diagnostics for the hand-proof ceiling 29B.

These checks do not establish the uniform sampling or asymptotic theorem.
Author: dot (OpenAI), working with Nolan, 17 October 2026.
"""
from fractions import Fraction as F
from itertools import product
import sympy as sp

p, q, ell, delta = sp.symbols('p q ell delta', real=True)
h = sp.Rational(1, 2)
mean = 0
for x, y in product((0, 1), repeat=2):
    f = x*y - (h+ell)*(x+y)/2 + h*ell
    mean += f * p**x * (1-p)**(1-x) * q**y * (1-q)**(1-y)
mean = sp.expand(mean)
assert sp.simplify(mean.subs({p:h,q:h})) == 0
assert sp.simplify(mean.subs({p:ell,q:ell})) == 0
for sign in (-1,1):
    assert sp.simplify(mean.subs({p:ell+sign*delta,q:ell-sign*delta})+delta**2) == 0
print('PASS: symbolic null means and sign-independent alternative mean')

lam, z = sp.symbols('lam z', positive=True)
assert sp.simplify(sp.integrate(sp.exp(lam*(z-1)),(z,0,1))-(1-sp.exp(-lam))/lam) == 0
print('PASS: exact Poisson inverse-count identity')

tests = 0
for pi in ((F(1),F(0),F(0)),(F(1,3),)*3,(F(1,100),F(9,100),F(9,10))):
    for counts in product(range(4),repeat=3):
        L=5
        split=[L+2*a for a in counts]
        assert sum(split)==3*L+2*sum(counts)
        for selected in ((0,),(1,2),(0,1,2)):
            left=sum(pi[i]**2/split[i] for i in selected)
            right=sum(pi[i] for i in selected)**2/sum(split[i] for i in selected)
            assert left>=right
            tests+=1
print('PASS:',tests,'rational weighted-Cauchy and split-size checks, including zero masses')

n,s,D,L,alpha=sp.symbols('n s D L alpha',positive=True)
tau=alpha**2*n**2/(8640*s*D*L)
assert sp.simplify(s*n/tau**2-8640**2*s**3*D**2*L**2/(alpha**4*n**3)) == 0
assert F(8640**2,10**18)<F(1,10**9)
assert F(1,4)*F(1,6)**2/F(5)==F(1,720)
assert F(1,720)/12==F(1,8640)
print('PASS: variance, signal and threshold constants')
print('SCOPE: exact finite/symbolic diagnostics; concentration and all-source claims remain hand-proof obligations.')
