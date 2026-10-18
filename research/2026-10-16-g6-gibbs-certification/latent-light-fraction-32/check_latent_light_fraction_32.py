"""Exact bounded checks for candidate32; not its parameterized proof.

Authored 2026-10-18 for Nolan's P1 research. Uses installed SymPy and
Python rational arithmetic only. No network, model calls, or simulation.
"""

from fractions import Fraction as F
from math import comb
import sympy as sp


def pair_coefficients(s, positives):
    """Per-pattern probability for t_j=x_1j*x_2j with given + count."""
    out = [F(0)] * (s + 1)
    for a in range(positives + 1):
        for b in range(s - positives + 1):
            out[a + b] += F(comb(positives, a) * comb(s - positives, b) * (-1) ** b)
    moment = F(1)
    for j in range(s + 1):
        if j:
            moment *= F(j + 2, j + 5)  # E[theta^j], theta~Beta(3,3)
        out[j] *= moment / (2 ** s)
    return out


def polynomial(coefficients, z):
    return sum(c * z ** j for j, c in enumerate(coefficients))


def derivative(coefficients, z):
    return sum(j * c * z ** (j - 1) for j, c in enumerate(coefficients) if j)


theta, z, delta, mu = sp.symbols("theta z delta mu", real=True)
f = 30 * theta ** 2 * (1 - theta) ** 2
h = (3 - 5 * theta) / (1 - theta)
assert sp.integrate(f, (theta, 0, 1)) == 1
assert sp.simplify(sp.diff(theta * f, theta) - h * f) == 0
assert sp.integrate(sp.cancel(f * h ** 2), (theta, 0, 1)) == 15
assert sp.integrate(sp.cancel(f * theta ** 2 / (1 - theta)), (theta, 0, 1)) == 1
assert (theta * f).subs(theta, 0) == (theta * f).subs(theta, 1) == 0

# Averaging the fixed symmetric perturbation changes a same-source pair's
# correlation by +4 delta^2 and a cross-source pair's by -4 delta^2.
r = sp.symbols("r", real=True)
assert sp.expand(((r + 2 * delta) ** 2 + (r - 2 * delta) ** 2) / 2 - r ** 2) == 4 * delta ** 2
assert sp.expand((r + 2 * delta) * (r - 2 * delta) - r ** 2) == -4 * delta ** 2

n = sp.symbols("n", integer=True, nonnegative=True)
fall2 = n * (n - 1)
fall3 = fall2 * (n - 2)
fall4 = fall3 * (n - 3)
assert sp.expand(n ** 2 * (n - 1) ** 2 - fall4 - 4 * fall3 - 2 * fall2) == 0
tilted_polynomial = sp.expand((6 * mu ** 2) ** 4 + 4 * (6 * mu ** 2) ** 3 + 2 * (6 * mu ** 2) ** 2)
assert tilted_polynomial == 1296 * mu ** 8 + 864 * mu ** 6 + 72 * mu ** 4
assert 1296 * (1 + F(1, 16)) == 1377
assert 4 * 1377 * 8 == 44064
assert 3840 * 8 == 30720
assert 65536 * (F(1, 2 ** 20) ** 3 + F(1, 2 ** 20) ** 5) < F(1, 2 ** 43)

# The exact mask denominator reduction's Poisson factors.
a, b = sp.symbols("a b", integer=True, nonnegative=True)
C_mu = sp.exp(-2 * mu) * mu ** (a + b) / (sp.factorial(a) * sp.factorial(b))
C_1 = sp.exp(-2) / (sp.factorial(a) * sp.factorial(b))
C_mu2 = sp.exp(-2 * mu ** 2) * mu ** (2 * (a + b)) / (sp.factorial(a) * sp.factorial(b))
assert sp.simplify(C_mu ** 2 / C_1 - sp.exp(2 - 4 * mu + 2 * mu ** 2) * C_mu2) == 0

cases = 0
for s in (8, 9, 12, 16):
    coefficients = [pair_coefficients(s, j) for j in range(s + 1)]
    z0 = (1 - F(2, s)) ** 2
    base = [polynomial(c, z0) for c in coefficients]
    assert all(p > 0 for p in base)
    assert sum(comb(s, j) * p for j, p in enumerate(base)) == 1
    for alpha in (F(1, 8), F(1, 4), F(1, 2)):
        d = alpha / s
        for direction in (-1, 1):
            test_z = z0 + direction * 4 * d ** 2
            probs = [polynomial(c, test_z) for c in coefficients]
            derivs = [derivative(c, test_z) for c in coefficients]
            assert test_z >= F(1, 2) and 1 - test_z >= F(3, s)
            assert all(p > 0 for p in probs)
            assert sum(comb(s, j) * p for j, p in enumerate(probs)) == 1
            fisher = sum(comb(s, j) * v * v / p for j, (v, p) in enumerate(zip(derivs, probs)))
            assert fisher <= 15 / test_z ** 2
            assert all(p <= 2 * p0 for p, p0 in zip(probs, base))
            fixed_norm = sum(comb(s, j) * v * v / p0 for j, (v, p0) in enumerate(zip(derivs, base)))
            assert fixed_norm <= 120
            chi = sum(comb(s, j) * (p - p0) ** 2 / p0 for j, (p, p0) in enumerate(zip(probs, base)))
            assert chi <= 1920 * alpha ** 4 / s ** 4
            cases += 1

# The old alphabet-centered statistic is not centered after unknown bit flips.
ell = sp.symbols("ell", positive=True)
p = sp.symbols("p", real=True)
mean = p ** 2 - (sp.Rational(1, 2) + ell) * p + ell / 2
assert sp.factor(mean) == (p - ell) * (2 * p - 1) / 2
assert sp.simplify(mean.subs(p, 1 - ell) - (1 - 2 * ell) * (sp.Rational(1, 2) - ell)) == 0

print("PASS: exact Beta normalization, integration-by-parts score and moments")
print("PASS: pair-correlation shifts, mask Poisson identity and factorial identities")
print(f"PASS: {cases} exact pair-row cases, including complete shared-latent averaging")
print("PASS: old fixed-alphabet centering fails on complemented light means")
print("Scope: bounded algebra checks; not an all-count or physical proof by computation")
