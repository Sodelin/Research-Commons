#!/usr/bin/env python3
"""Deterministic replay of a randomized paired/avoiding construction."""
from math import gcd
from random import Random

def build(w, blocks_per_residue, denominator, seed):
    n = 2*w*blocks_per_residue
    rng = Random(seed)
    yes, no = set(), set()
    for a in range(1,w//2):
        if gcd(a,w) != 1: continue
        for j in range(blocks_per_residue):
            if rng.randrange(denominator) >= 2: continue
            i = rng.randrange(2)
            u = a+(2*j+i)*w
            alt = a+(2*j+1-i)*w
            yes.update((u,n-u))
            no.update((u,n-alt))
    return n, yes, no

def main():
    # Rounded-up tail envelope: log(2N)*6 < 6*bit_length(2N).
    w, b, d, seed = 30, 180, 10, 2626
    n, yes, no = build(w,b,d,seed)
    assert yes and len(yes) == len(no)
    assert all(n-x in yes for x in yes)
    assert not any(n-x in no for x in no)
    assert all(gcd(x,w)==1 for x in yes|no)
    eligible = [x for x in range(1,n) if gcd(x,w)==1]
    z = 6*(2*n).bit_length()
    tested, metric = 0, 0
    for q in range(1,81):
        counts = [[0]*q for _ in range(3)]
        for x in eligible:
            r = x%q
            counts[0][r] += 1
            counts[1][r] += x in yes
            counts[2][r] += x in no
            for k in (1,2):
                discrepancy = abs(d*counts[k][r]-counts[0][r])
                metric = max(metric, discrepancy)
                # Test |count−m/d| <= sqrt(4*m*z/d)+4*z/3 exactly.
                rest = max(0,3*discrepancy - 4*d*z)
                assert rest*rest <= 36*d*counts[0][r]*z
                tested += 1
        if w%q == 0:
            assert counts[1] == counts[2]
    print(f"N={n}, ordered pair counts {len(yes)} vs 0")
    print(f"{tested} exact residue-prefix envelope checks over moduli 1..80")
    print(f"Largest observed |count - eligible/d| = {metric}/{d}")
    n = 12000
    rng = Random(20261123)
    chosen = []
    for a in range(1,n//2,2):
        v = rng.randrange(10)
        if v < 2:
            chosen.append(a if v == 0 else n-a)
    sums = {a+b for i,a in enumerate(chosen) for b in chosen[i:]}
    misses = [t for t in range(n//2,3*n//2+1,2) if t not in sums]
    assert misses == [n]
    print(f"Isolated-miss fixture: {len(chosen)} selected odds; misses={misses}")
    for n in range(192,200000,210):
        assert (n//2-1)%5 == (n//3-1)%7 == 0
        assert n//2-1>5 and n//3-1>7
    print("CRT fixture: all 952 members of 192 mod 210 up to 200000 pass")
if __name__ == "__main__":
    main()
