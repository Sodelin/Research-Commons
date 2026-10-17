"""Exact finite checks for candidate 29, not a parameterized proof.

Author: dot (OpenAI), working with Nolan. 17 October 2026.
Only standard Python and the already installed SymPy are used.
"""

from itertools import product
from math import comb
import sympy as sp


def bernoulli_word(word, p):
    return p ** sum(word) * (1 - p) ** (len(word) - sum(word))


def falling(n, j):
    return 0 if n < j else sp.factorial(n) / sp.factorial(n - j)


def check_case(s, alpha, a, b):
    ell, h = sp.Rational(1, s), sp.Rational(1, 2)
    delta = alpha / s
    n = a + b
    d = sp.S.Zero
    mass0 = mass1 = sp.S.Zero
    for word in product((0, 1), repeat=n):
        first, second = word[:a], word[a:]
        heavy = bernoulli_word(word, h)
        light = bernoulli_word(word, ell)
        plus = bernoulli_word(first, ell + delta) * bernoulli_word(second, ell - delta)
        minus = bernoulli_word(first, ell - delta) * bernoulli_word(second, ell + delta)
        null = (heavy + light) / 2
        alternative = heavy / 2 + (plus + minus) / 4
        assert null > 0
        mass0 += null
        mass1 += alternative
        d += (alternative - null) ** 2 / null
    assert mass0 == mass1 == 1
    assert d >= 0
    if n < 2:
        assert d == 0

    v = sp.Rational(1, 4)
    x = (abs(ell - h) + delta) ** 2 / v
    assert 0 <= x <= 1
    terms = [(4, x ** 2), (3, 4 * x), (2, sp.Integer(2))]
    bound6 = delta ** 4 / (8 * v ** 2) * sum(
        falling(n, j) * coefficient * (1 + x) ** (n - j)
        for j, coefficient in terms if n >= j
    )
    coarse6 = 2 * delta ** 4 * n ** 2 * (n - 1) ** 2 * 2 ** n
    y = alpha ** 2 / (s - 1)
    bound7 = ((1 + y) ** n - 1) / 2
    assert d <= bound6 <= coarse6
    assert d <= bound7

    row_chi2 = (1 + d) ** s - 1
    bound8 = 2 * alpha ** 4 / s ** 3 * n ** 2 * (n - 1) ** 2 * 3 ** n
    assert row_chi2 <= bound8
    return d, row_chi2


case_count = 0
for s, alpha, a, b in product(
    (3, 4, 6), (sp.Rational(1, 2), sp.Rational(1, 4), sp.Rational(1, 8)), range(4), range(4)
):
    check_case(s, alpha, a, b)
    case_count += 1
print(f"PASS: {case_count} exact rational coordinate and product-row cases")

# The shared-coordinate tensor product identity itself, checked by explicit
# summation in four small nontrivial experiments rather than assumed in code.
tensor_count = 0
for s, alpha, a, b in ((3, sp.Rational(1, 2), 1, 1),
                       (3, sp.Rational(1, 4), 2, 0),
                       (4, sp.Rational(1, 2), 1, 1),
                       (3, sp.Rational(1, 8), 0, 2)):
    n = a + b
    ell, h, delta = sp.Rational(1, s), sp.Rational(1, 2), alpha / s
    single = []
    for word in product((0, 1), repeat=n):
        first, second = word[:a], word[a:]
        heavy = bernoulli_word(word, h)
        null = (heavy + bernoulli_word(word, ell)) / 2
        plus = bernoulli_word(first, ell + delta) * bernoulli_word(second, ell - delta)
        minus = bernoulli_word(first, ell - delta) * bernoulli_word(second, ell + delta)
        alt = heavy / 2 + (plus + minus) / 4
        single.append((null, alt))
    direct = sp.S.Zero
    for choices in product(single, repeat=s):
        null = sp.prod(p[0] for p in choices)
        alt = sp.prod(p[1] for p in choices)
        direct += (alt - null) ** 2 / null
    _, row = check_case(s, alpha, a, b)
    assert direct == row
    tensor_count += 1
print(f"PASS: {tensor_count} explicit full-row tensor likelihood checks")

# Exact finite-dimensional mixture-denominator identity, for arbitrary
# positive count weights. These rational weights are algebraic placeholders,
# not approximate Poisson probabilities.
mixture_count = 0
for mu, c1, cm in product(
    (sp.Rational(1, 4), sp.Rational(1, 8)),
    (sp.Rational(1, 3), sp.Rational(2, 5)),
    (sp.Rational(1, 7), sp.Rational(3, 8))
):
    null_data = (sp.Rational(1, 3), sp.Rational(2, 3))
    alt_data = (sp.Rational(1, 4), sp.Rational(3, 4))
    denominator = mu * c1 + (1 - mu) * cm
    direct = sum(
        ((mu * c1 * p + (1 - mu) * cm * q) - denominator * p) ** 2
        / (denominator * p)
        for p, q in zip(null_data, alt_data)
    )
    data_chi = sum((q - p) ** 2 / p for p, q in zip(null_data, alt_data))
    exact = (1 - mu) ** 2 * cm ** 2 / denominator * data_chi
    assert direct == exact
    assert exact <= cm ** 2 / (mu * c1) * data_chi
    mixture_count += 1
print(f"PASS: {mixture_count} exact shared-mass mixture-denominator checks")

j = sp.symbols('j', integer=True)
assert sp.expand((j * (j - 1)) ** 2 -
                 (j * (j - 1) * (j - 2) * (j - 3) +
                  4 * j * (j - 1) * (j - 2) + 2 * j * (j - 1))) == 0
mu, z = sp.symbols('mu z', positive=True)
pgf = sp.exp(2 * mu ** 2 * (z - 1))
moment = sum(coefficient * z ** order * sp.diff(pgf, z, order)
             for order, coefficient in ((4, 1), (3, 4), (2, 2)))
assert sp.simplify(moment.subs(z, 3) -
                   (1296 * mu ** 8 + 864 * mu ** 6 + 72 * mu ** 4)
                   * sp.exp(4 * mu ** 2)) == 0
assert (1296 * mu ** 4 + 864 * mu ** 2 + 72).subs(mu, sp.Rational(1, 4)) < 132
assert sp.Rational(4096, 1600 ** 3) == sp.Rational(1, 10 ** 6)
print("PASS: falling-factorial identity, Poisson PGF polynomial, endpoint and budget constants")

# The Poisson density quotient identity, without numerical exponentials.
n = sp.symbols('n', integer=True, nonnegative=True)
lhs = sp.exp(-4 * mu + 2) * mu ** (2 * n)
rhs = sp.exp(2 - 4 * mu + 2 * mu ** 2) * sp.exp(-2 * mu ** 2) * (mu ** 2) ** n
assert sp.simplify(lhs - rhs) == 0
print("PASS: exact Poisson density quotient, retaining the two-source joint count")
print("Finite checks supplement the candidate hand proof; no asymptotic theorem is inferred from enumeration.")
