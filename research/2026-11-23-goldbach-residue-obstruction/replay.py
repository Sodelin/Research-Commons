#!/usr/bin/env python3
"""Exact finite replay of the residue-preserving Goldbach obstruction."""
from math import gcd, lcm


def construct(w, d, blocks):
    assert w > 2 and w % 2 == 0 and d >= 2 and blocks >= 1
    n = w * d * blocks
    paired, avoided = set(), set()
    for r in range(1, w // 2):
        if gcd(r, w) != 1:
            continue
        for j in range(0, d * blocks, d):
            a = r + j * w
            paired.update((a, n - a))
            avoided.update((a, n - a - w))
    return n, paired, avoided


def verify(w, d, blocks):
    n, paired, avoided = construct(w, d, blocks)
    eligible = [x for x in range(1, n) if gcd(x, w) == 1]
    assert len(paired) == len(avoided) == len(eligible) // d
    assert sum(n - x in paired for x in paired) == len(paired)
    assert not any(n - x in avoided for x in avoided)
    assert paired <= set(eligible) and avoided <= set(eligible)

    by_residue = [[[] for _ in range(w)] for _ in range(2)]
    for k, values in enumerate((paired, avoided)):
        for x in sorted(values):
            by_residue[k][x % w].append(x)
    for r, (a, b) in enumerate(zip(*by_residue)):
        if gcd(r, w) != 1:
            assert not a and not b
            continue
        assert len(a) == len(b) == blocks
        assert all(abs(x-y) <= w for x, y in zip(a, b))

    checks = 0
    # For one residue, its prefix counts only change at eligible entries
    # in that residue; the empty prefix is automatic.
    for q in (q for q in range(1, w + 1) if w % q == 0):
        widths = [0] * q
        for r in range(w):
            if gcd(r, w) == 1:
                widths[r % q] += 1
        counts = [[0] * q for _ in range(3)]
        for x in eligible:
            r = x % q
            counts[0][r] += 1
            counts[1][r] += x in paired
            counts[2][r] += x in avoided
            for k in (1, 2):
                assert abs(d * counts[k][r] - counts[0][r]) < d * widths[r]
                checks += 1
        assert counts[0] == [d * x for x in counts[1]]
        assert counts[1] == counts[2]
    return n, len(paired), checks


if __name__ == "__main__":
    total = 0
    for w, d, blocks in [(6, 2, 1), (30, 3, 9), (210, 5, 16),
                           (lcm(*range(1, 12)), 7, 2), (14, 6, 19)]:
        n, ordered_pairs, checks = verify(w, d, blocks)
        total += checks
        print(f"W={w} d={d} N={n}: ordered pairs {ordered_pairs} vs 0; checks={checks}")
    print(f"Total exact prefix checks: {total}")
