"""Independent bounded diagnostics for candidate29's statistical argument.

Written from the candidate's distributions, without importing the author's
checker. Exact rational enumeration of sufficient statistics checks (6)--(8).
The unbounded-count and asymptotic conclusions remain hand proofs.
"""
from fractions import Fraction as F
from math import comb, factorial, exp
from hashlib import sha256
from pathlib import Path


def probability(a, b, i, j, p, q):
    return (comb(a, i) * comb(b, j) * p**i * (1-p)**(a-i)
            * q**j * (1-q)**(b-j))


def coordinate(s, alpha, a, b):
    ell, h, delta = F(1, s), F(1, 2), alpha/s
    p0, p1 = [], []
    for i in range(a+1):
        for j in range(b+1):
            heavy = probability(a, b, i, j, h, h)
            light = probability(a, b, i, j, ell, ell)
            signed = (probability(a, b, i, j, ell+delta, ell-delta)
                      + probability(a, b, i, j, ell-delta, ell+delta))/2
            p0.append((heavy+light)/2)
            p1.append((heavy+signed)/2)
    assert sum(p0) == sum(p1) == 1
    d = sum((q-p)**2/p for p, q in zip(p0, p1))
    return d, p0, p1


source = Path(__file__).with_name('P1-RANDOM-LABEL-MASS-CANDIDATE-29.md')
expected = '40038740c2e6e3cddd8b50f6f67b3078ddcc8d82415727fd0ea72783c7599bbd'
assert sha256(source.read_bytes()).hexdigest() == expected
print('PASS: candidate source SHA256', expected)

cases = 0
largest_ratios = [0.0, 0.0, 0.0]
for s in (10, 17, 32):
    for alpha in (F(1, 2), F(1, 4), F(1, 16)):
        for n in range(9):
            for a in range(n+1):
                b = n-a
                d, p0, p1 = coordinate(s, alpha, a, b)
                if n < 2:
                    assert d == 0
                delta, y = alpha/s, alpha**2/(s-1)
                bound6 = 2*delta**4*n*n*(n-1)*(n-1)*2**n
                bound7 = ((1+y)**n-1)/2
                data = (1+d)**s-1
                bound8 = 2*alpha**4/F(s**3)*n*n*(n-1)*(n-1)*3**n
                assert d <= bound6
                assert d <= bound7
                assert data <= bound8
                for j, (value, bound) in enumerate(((d, bound6), (d, bound7), (data, bound8))):
                    if bound:
                        largest_ratios[j] = max(largest_ratios[j], float(value/bound))
                cases += 1
print('PASS: exact rational coordinate / complete-row bounds in', cases, 'count-allocation cases')
print('Max checked ratios to bounds (6), (7), (8):', largest_ratios)

# A literal two-coordinate joint-outcome calculation checks that sharing one
# hidden mass type is a single mixture, rather than two independent mixtures.
# The rational count weights here test the algebraic identity in (9); the
# actual Poisson weights and their infinite sum are handled in the hand proof.
d, p0, p1 = coordinate(10, F(1, 2), 1, 1)
mu, c_heavy, c_light = F(1, 5), F(2, 7), F(3, 11)
den = mu*c_heavy+(1-mu)*c_light
direct = 0
for i in range(len(p0)):
    for j in range(len(p0)):
        n_density = den*p0[i]*p0[j]
        a_density = mu*c_heavy*p0[i]*p0[j]+(1-mu)*c_light*p1[i]*p1[j]
        direct += (a_density-n_density)**2/n_density
factored = (1-mu)**2*c_light**2/den*((1+d)**2-1)
assert direct == factored
print('PASS: exact joint-data shared-mass-mixture denominator identity')

# Polynomial identity used by the all-count hand bound.
for n in range(20):
    fall = lambda j: factorial(n)//factorial(n-j) if n >= j else 0
    assert n*n*(n-1)*(n-1) == fall(4)+4*fall(3)+2*fall(2)
assert F(4096, 1600**3) == F(1, 10**6)
assert 1296*F(1,4)**4+864*F(1,4)**2+72 == F(2097, 16) < 132
assert 2*132*exp(2) < 4096
assert (2/3)*exp(-3) > 1/48
assert 0.5*(exp(1e-6)-1)**0.5 < 0.001
print('PASS: finite polynomial and numerical constant diagnostics')
print('SCOPE: bounded exact diagnostics; no physical-encoding, all-size, or Lean verification')
