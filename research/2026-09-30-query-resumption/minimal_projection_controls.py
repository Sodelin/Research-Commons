"""Finite controls for exact sparse moment and circular distance shadows.

The moments are explicitly stronger aggregate measurements, not legal quartet
oracle calls. This script does not claim a sparse acquisition algorithm.
"""
from itertools import combinations
from pathlib import Path
import importlib.util
import json
import math
import random


def prime_above(m):
    p = m + 1
    while p < 2 or any(p % q == 0 for q in range(2, math.isqrt(p) + 1)):
        p += 1
    return p


def encode_moments(support, p):
    return [len(support)] + [sum(pow(x, j, p) for x in support) % p
                             for j in range(1, len(support) + 1)]


def decode_moments(sums, m, p):
    k = sums[0]
    assert 0 <= k <= m < p and len(sums) == k + 1
    elementary = [1]
    for j in range(1, k + 1):
        e = sum((1 if i % 2 else -1) * elementary[j - i] * sums[i]
                for i in range(1, j + 1)) * pow(j, -1, p)
        elementary.append(e % p)
    coefficients = [((1 if j % 2 == 0 else -1) * elementary[j]) % p
                    for j in range(k + 1)]
    roots = set()
    for x in range(1, m + 1):
        value = 0
        for c in coefficients:
            value = (value * x + c) % p
        if value == 0:
            roots.add(x)
    assert len(roots) == k
    return roots


def split_gap_dictionary(n):
    full = (1 << n) - 1
    ans = {}
    for i, j in combinations(range(n), 2):
        if j == i + 1 or (i == 0 and j == n - 1):
            continue
        side = sum(1 << t for t in range(i + 1, j + 1))
        ans[(i, j)] = min(side, full ^ side)
    assert len(ans) == n * (n - 3) // 2
    return ans


def shadow_distance(splits, n):
    return [[0 if a == b else 2 + sum(bool(s & (1 << a)) !=
                                     bool(s & (1 << b)) for s in splits)
             for b in range(n)] for a in range(n)]


def invert_distance(d, n):
    coefficients = {}
    for gaps, split in split_gap_dictionary(n).items():
        i, j = gaps
        a, b, c, e = i, (i + 1) % n, j, (j + 1) % n
        twice = d[a][c] + d[b][e] - d[a][e] - d[b][c]
        assert twice in (0, 2)
        coefficients[split] = twice // 2
    return {s for s, c in coefficients.items() if c}


def topology_support(splits, q):
    full = sum(1 << t for t in q)
    return {min(s & full, full ^ (s & full)) for s in splits
            if (s & full).bit_count() == 2}


def run():
    rng = random.Random(20260930)
    exhaustive_moments = randomized_moments = distances = quartet_checks = 0
    for m in range(1, 13):
        p = prime_above(m)
        seen = set()
        for bitset in range(1 << m):
            support = {i + 1 for i in range(m) if bitset & (1 << i)}
            sums = encode_moments(support, p)
            assert decode_moments(sums, m, p) == support
            assert tuple(sums) not in seen
            seen.add(tuple(sums))
            exhaustive_moments += 1
    for n in range(4, 61):
        gaps = split_gap_dictionary(n)
        m = len(gaps)
        p = prime_above(m)
        candidates = list(gaps.values())
        for _ in range(5):
            k = rng.randint(0, min(m, 13 * n - 27))
            support = set(rng.sample(range(1, m + 1), k))
            assert decode_moments(encode_moments(support, p), m, p) == support
            randomized_moments += 1
            # These circular split families need not be source-admitted.
            splits = {candidates[i - 1] for i in support}
            assert invert_distance(shadow_distance(splits, n), n) == splits
            distances += 1

    # Source-admitted level-two fixtures: recheck support-table regeneration
    # from the saved exact switching/graph receipt, without importing its oracle.
    receipt = Path(__file__).resolve().parent.parent / (
        '2026-09-30-root-exact-query/anchor-collision-receipt.json')
    original = json.loads(receipt.read_text())
    source_fixtures = []
    n = 5
    full = (1 << n) - 1
    candidates = list(split_gap_dictionary(n).values())
    for fix in original['fixtures']:
        all_splits = {min(sum(1 << int(t[1:]) for t in s),
                          full ^ sum(1 << int(t[1:]) for t in s))
                      for s in fix['displayed_splits']}
        splits = {s for s in all_splits if 2 <= s.bit_count() <= n - 2}
        assert splits.issubset(candidates)
        shadow = shadow_distance(splits, n)
        assert invert_distance(shadow, n) == splits
        support_indices = {candidates.index(s) + 1 for s in splits}
        p = prime_above(len(candidates))
        sums = encode_moments(support_indices, p)
        assert decode_moments(sums, len(candidates), p) == support_indices
        for q in combinations(range(n), 4):
            mask = sum(1 << t for t in q)
            saved = {min(sum(1 << int(t[1:]) for t in pair),
                         mask ^ sum(1 << int(t[1:]) for t in pair))
                     for pair in fix['quartets'][''.join(map(str, q))]}
            assert topology_support(splits, q) == saved
            quartet_checks += 1
        source_fixtures.append({'name': fix['name'], 'nontrivial_splits': len(splits),
                                'support_indices': sorted(support_indices),
                                'prime': p, 'moments': sums,
                                'distance_shadow': shadow})
    return {'status': 'PASS', 'exhaustive_sparse_moment_decodings': exhaustive_moments,
            'random_sparse_moment_decodings': randomized_moments,
            'random_circular_distance_inversions': distances,
            'saved_source_fixture_quartet_regenerations': quartet_checks,
            'source_fixtures': source_fixtures,
            'scope': 'Finite algebra controls; aggregate moment access is not executed as legal quartet queries. Generic random circular families are not source witnesses.'}


if __name__ == '__main__':
    result = run()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
