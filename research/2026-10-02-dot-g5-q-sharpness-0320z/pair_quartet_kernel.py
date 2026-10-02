"""Exact all-partitions kernel for G5's unresolved binary Q panel threshold.

This is a fixed 4-label, 2-equiprobable-position theorem check, not a network
or calendar sample. Bell(8)=4140 is the proved complete finite domain.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import platform

PAIR_ORDER = tuple(combinations(range(4), 2))
SPLITS = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))


def restricted_growth_strings(n):
    """Each set partition exactly once, by its unique first-appearance names."""
    def visit(prefix, maximum):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for value in range(maximum + 2):
            yield from visit(prefix + [value], max(maximum, value))
    yield from visit([0], 0)


def counts(rgs):
    result = [[0] * 4 for _ in range(max(rgs) + 1)]
    for occurrence, block in enumerate(rgs):
        result[block][occurrence // 2] += 1
    return tuple(tuple(row) for row in result)


def moments(rows):
    return tuple(sum(row[i] * row[j] for row in rows) for i, j in PAIR_ORDER)


def witness_mask(rows):
    return tuple(any((row[a] > 0 and row[b] > 0 and row[c] < 2 and row[d] < 2)
                     or (row[c] > 0 and row[d] > 0 and row[a] < 2 and row[b] < 2)
                     for row in rows)
                 for (a, b), (c, d) in SPLITS)


def moment_criterion(vector, a, b, c, d):
    K = {pair: value for pair, value in zip(PAIR_ORDER, vector)}
    def k(i, j):
        return K[tuple(sorted((i, j)))]
    cross = (k(a, c), k(a, d), k(b, c), k(b, d))
    if 4 in cross:
        return False
    u, v = k(a, b), k(c, d)
    if u == v == 0:
        return False
    def blocked_positive_side(u, v, ac, ad, bc, bd):
        return v == 0 and ((u == 1 and ((ac == bc == 2) or (ad == bd == 2)))
                           or (u == 2 and ac == ad == bc == bd == 2))
    if blocked_positive_side(u, v, *cross):
        return False
    if blocked_positive_side(v, u, cross[0], cross[2], cross[1], cross[3]):
        return False
    return True


def weighted_moments(distributions):
    positions = set().union(*(set(row) for row in distributions))
    return tuple(sum(distributions[i].get(e, 0) * distributions[j].get(e, 0)
                     for e in positions) for i, j in PAIR_ORDER)


def weighted_witness(distributions, a, b, c, d):
    S = [set(row) for row in distributions]
    def side(a, b, c, d):
        return any(S[c] != {e} and S[d] != {e} for e in S[a] & S[b])
    return side(a, b, c, d) or side(c, d, a, b)


def main():
    fibers, partitions, tests = {}, 0, 0
    entries = []
    for rgs in restricted_growth_strings(8):
        rows = counts(rgs)
        K, W = moments(rows), witness_mask(rows)
        assert all(value in (0, 1, 2, 4) for value in K)
        assert all(sum(row[i] for row in rows) == 2 for i in range(4))
        assert W == tuple(moment_criterion(K, *ab, *cd) for ab, cd in SPLITS)
        if K in fibers:
            assert fibers[K]['witness_mask'] == list(W)
            fibers[K]['partitions'] += 1
        else:
            fibers[K] = {'pair_counts': list(K), 'witness_mask': list(W),
                         'representative_rgs': list(rgs), 'partitions': 1}
        partitions += 1
        tests += 3
    assert partitions == 4140 and len(fibers) == 403
    half, quarter = Fraction(1, 2), Fraction(1, 4)
    A = ({'e': half, 'h': half}, {'e': half, 'k': half}, {'e': Fraction(1)}, {'l': Fraction(1)})
    B = ({'u': Fraction(1)}, {'u': quarter, 'v': 3 * quarter},
         {'u': half, 'v': half}, {'l': Fraction(1)})
    assert weighted_moments(A) == weighted_moments(B)
    assert not weighted_witness(A, 0, 1, 2, 3)
    assert weighted_witness(B, 0, 1, 2, 3)
    kernel = {'pair_order': [list(p) for p in PAIR_ORDER],
              'split_order': [[list(a), list(b)] for a, b in SPLITS],
              'fibers': sorted(fibers.values(), key=lambda row: row['pair_counts'])}
    Path(__file__).with_name('kernel.json').write_text(json.dumps(kernel, indent=2) + '\n')
    report = {'status': 'PASS', 'partitions': partitions, 'moment_fibers': len(fibers),
              'split_predicate_tests': tests, 'criterion_tests': tests,
              'kernel_conflicting_fibers': 0,
              'fiber_partition_counts_total': sum(row['partitions'] for row in fibers.values()),
              'mask_fiber_counts': dict(Counter(''.join(map(lambda x: str(int(x)), row['witness_mask'])) for row in fibers.values())),
              'weighted_fixed_time_counterexample': {'pair_moments': [str(v) for v in weighted_moments(A)],
                                                    'A_ab_cd_witness': False, 'B_ab_cd_witness': True,
                                                    'scope': 'Categorical Cartesian position distributions only; not complete calendar source laws'},
              'scope': 'Complete fixed 4-label/two-equiprobable-occurrence partition lemma; all-clock terminal-source transfer is proved separately',
              'python': platform.python_version(),
              'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name('results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
