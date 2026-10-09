"""Bounded exact controls only; does not execute source membership/cutoffs."""
from math import comb
from fractions import Fraction
import json

LAM = (1, 3, 6, 10, 15, 21)

def exponents(total, width):
    if width == 1:
        yield (total,)
    else:
        for a in range(total + 1):
            for tail in exponents(total - a, width - 1):
                yield (a,) + tail

def det(a):
    a = [[Fraction(x) for x in row] for row in a]
    out = Fraction(1)
    for k in range(len(a)):
        j = next(j for j in range(k, len(a)) if a[j][k])
        if j != k:
            a[k], a[j] = a[j], a[k]
            out = -out
        pivot = a[k][k]
        out *= pivot
        for j in range(k + 1, len(a)):
            ratio = a[j][k] / pivot
            for i in range(k, len(a)):
                a[j][i] -= ratio * a[k][i]
    return out

degrees = [x - 1 for x in LAM]
matrix = [[(lam + 1 if power == 0 else int(power < lam))
           for lam in LAM] for power in degrees]
assert det(matrix) == 2
rows = []
for degree in range(1, 7):
    denominator = degree + 1
    scale = denominator ** 20
    weights = [scale * lam + sum(denominator ** (20-j) for j in range(lam))
               for lam in LAM]
    seen = set()
    count = 0
    for total in range(degree + 1):
        for alpha in exponents(total, 6):
            weight = sum(x*y for x, y in zip(alpha, weights))
            assert weight not in seen
            seen.add(weight)
            count += 1
    assert count == comb(degree + 6, 6)
    rows.append(dict(degree=degree, residue_denominator=denominator,
                     monomials=count, distinct_weights=len(seen)))
print(json.dumps(dict(status="PASS", coefficient_minor_determinant="2",
                     checks=rows,
                     not_executed=["small-loss cutoff extraction", "source membership",
                                   "original response compiler", "QE", "Lean"]), indent=2))
