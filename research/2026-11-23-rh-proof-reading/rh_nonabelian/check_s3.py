#!/usr/bin/env python3
"""Exact S3 character/Euler-factor checks; no numerical zero computation."""
from collections import Counter
from itertools import permutations
from math import isqrt

ONE = (1,)
T = (1, -1)
TPLUS = (1, 1)
Q = (1, 1, 1)

def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            c[i+j] += ai * bj
    return tuple(c)

def power(a, k):
    b = ONE
    for _ in range(k):
        b = mul(a, b)
    return b

def factor_cycle_lengths(p):
    seen, lengths = set(), []
    for i in range(len(p)):
        if i in seen:
            continue
        j, size = i, 0
        while j not in seen:
            seen.add(j)
            j = p[j]
            size += 1
        lengths.append(size)
    return tuple(sorted(lengths))

SIGNS = {(1, 1, 1): 1, (1, 2): -1, (3,): 1}
STANDARD = {(1, 1, 1): power(T, 2), (1, 2): mul(T, TPLUS), (3,): Q}

def local_zeta(cycles):
    a = ONE
    for k in cycles:
        a = mul(a, (1,) + (0,) * (k - 1) + (-1,))
    return a

def type_by_roots(p):
    roots = tuple(x for x in range(p) if (x**3-2) % p == 0)
    return {0: (3,), 1: (1, 2), 3: (1, 1, 1)}[len(roots)], roots

def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))

def main():
    G = list(permutations(range(3)))
    for p in G:
        ct = factor_cycle_lengths(p)
        order = max(ct)   # in S3 each possible type has max cycle = permutation order
        std = ct.count(1)-1
        sign = SIGNS[ct]
        assert 1+sign+2*std == (6 if order == 1 else 0)
        assert local_zeta(ct) == mul(T, STANDARD[ct])
        assert local_zeta((order,) * (6//order)) == mul(
            mul(T, (1,-sign)), power(STANDARD[ct], 2))
    assert local_zeta((1,)) == mul(T, ONE)  # cubic field at both 2 and 3
    assert local_zeta((2,)) == mul(T, (1, 1))  # normal closure at 2
    assert local_zeta((1,)) == mul(T, ONE)  # normal closure at 3
    print("S3 regular and cubic permutation characters and Euler identities: PASS.")
    counts = Counter()
    for p in range(5, 1000):
        if is_prime(p):
            ct, roots = type_by_roots(p)
            counts[ct] += 1
            assert ct == (((1,1,1) if pow(2,(p-1)//3,p) == 1 else (3,)) if p % 3 == 1 else (1,2))
            assert SIGNS[ct] == (1 if p % 3 == 1 else -1)
            assert -STANDARD[ct][1] == 3*(ct == (1,1,1))-(p % 3 == 1)
            if p in (5, 7, 31):
                print(f"p={p}: mod3={p % 3}, roots={roots}, cycles={ct}, standard Euler polynomial={STANDARD[ct]}")
    print("Exact unramified prime fixtures below 1000:", sorted(counts.items()))
    assert type_by_roots(7) == ((3,), ())
    assert type_by_roots(31) == ((1,1,1), (4,7,20))
    assert counts == {(1,1,1): 24, (1,2): 86, (3,): 56}

def check_eta_product(bound=999):
    # q * product_{n>=1}(1-q^(6n))(1-q^(18n)).
    exp = [0]*(bound+1)
    exp[1] = 1
    for step in (6,18):
        for k in range(step,bound,step):
            for j in range(bound,k,-1):
                exp[j] -= exp[j-k]
    primes = [p for p in range(2,bound+1) if is_prime(p)]
    for n in range(1,bound+1):
        m, expected = n, 1
        for p in primes:
            if p > m:
                break
            k = 0
            while m % p == 0:
                m //= p
                k += 1
            if not k:
                continue
            if p in (2,3):
                a = 0
            else:
                ct, _ = type_by_roots(p)
                a = {
                    (1,1,1): k+1,
                    (1,2): 1 if k % 2 == 0 else 0,
                    (3,): (1,-1,0)[k % 3],
                }[ct]
            expected *= a
        assert m == 1
        assert exp[n] == expected, (n,exp[n],expected)
    print(f"Eta-product and Artin Dirichlet coefficients agree for all 1 <= n <= {bound}.")

if __name__ == '__main__':
    main()
    check_eta_product()
