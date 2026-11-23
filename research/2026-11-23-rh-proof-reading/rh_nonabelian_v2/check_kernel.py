#!/usr/bin/env python3
"""Exact finite algebra fixtures for the compact-window criterion."""
from fractions import Fraction as Q


def w(r, u):
    if 1 <= u <= r:
        return r * (1 - 1/u)
    if r <= u <= r*r:
        return r*r/u - 1
    return Q(0)


def from_dilations(r, u):
    k = lambda q: max(Q(0), q-1)
    return k(r*r/u) - (1+r)*k(r/u) + r*k(1/u)


def monomial(a, b, k):
    return (b**k-a**k)/k


scales = [Q(6, 5), Q(3, 2), Q(2), Q(3), Q(4)]
checks = moments = 0
for r in scales:
    points = {Q(i, j) for i in range(1, 100) for j in range(1, 20)}
    points.update([Q(1), r, r*r])
    for u in points:
        a = w(r, u)
        assert a == from_dilations(r, u)
        assert 0 <= a <= r-1
        assert (a > 0) == (1 < u < r*r)
        checks += 1
    assert w(r, r) == r-1
    for s in [-5, -4, -3, -2, -1, 2, 3, 4, 5, 6, 7]:
        integral = (r*monomial(Q(1), r, s) - r*monomial(Q(1), r, s-1)
                    + r*r*monomial(r, r*r, s-1) - monomial(r, r*r, s))
        multiplier = (r**s-1)*(r**s-r)/(s*(s-1))
        assert integral == multiplier > 0
        moments += 1

print(f"PASS: {checks} exact compact-window weight fixtures at {len(scales)} rational scales")
print(f"PASS: {moments} exact nonexceptional integer Mellin moment identities")
print("NO TEST CLAIM: infinite-window estimate, zero verification, or Lean compilation")
