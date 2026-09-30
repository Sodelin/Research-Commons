"""Exhaustive finite contract checks for abstaining_recovery.py."""
from itertools import combinations, product
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, sys, time
from sparse_quartet import (shapes, graph_from_shape, selected_tree_split_union,
                            split_support_oracle)
from abstaining_recovery import recover_with_abstention

HERE = Path(__file__).resolve().parent


def main():
    if not __debug__:
        raise RuntimeError('Do not run with -O')
    start = time.perf_counter()
    n = 5
    trees = [selected_tree_split_union(graph_from_shape(s, n), [[i] for i in range(n)])
             for s in shapes(1, n)]
    families = set()
    for mask in range(1, 1 << len(trees)):
        families.add(frozenset().union(*(trees[i] for i in range(len(trees)) if mask >> i & 1)))
    quartets = list(combinations(range(n), 4))
    counts = {'tables': 0, 'complete_correct': 0, 'inconclusive': 0}
    for support in sorted(families, key=lambda s: sorted(s)):
        exact = split_support_oracle(n, support)
        truth = {q: exact(q) for q in quartets}
        options = []
        for q in quartets:
            t = truth[q]
            other = sorted({1, 4, 5} - {t})
            options.append([frozenset({t}), frozenset({t, other[0]}),
                            frozenset({t, other[1]}), frozenset({1, 4, 5})])
        for values in product(*options):
            table = dict(zip(quartets, values))
            r = recover_with_abstention(n, table.__getitem__)
            counts['tables'] += 1
            if r.status == 'complete':
                assert r.recovery is not None and r.recovery.splits == support
                counts['complete_correct'] += 1
            else:
                assert r.recovery is None and r.unresolved_quartet is not None
                assert len(r.candidate_masks) > 1
                counts['inconclusive'] += 1
            assert r.oracle_calls <= min(len(quartets), (n-2)*(n-3))
    empty = recover_with_abstention(4, lambda q: ())
    assert empty.status == 'inconclusive' and empty.reason == 'empty confidence set'
    assert empty.recovery is None
    conservative = recover_with_abstention(4, lambda q: {4, 5})
    assert conservative.status == 'inconclusive'
    wrong = recover_with_abstention(4, lambda q: {1})
    truth = frozenset({(0, 2)})  # The real support would have quartet mask 4.
    assert wrong.status == 'complete' and wrong.recovery.splits != truth
    malformed = 0
    for candidate in [{0}, {2}, {8}, {True}]:
        try:
            recover_with_abstention(4, lambda q, c=candidate: c)
        except ValueError:
            malformed += 1
        else:
            raise AssertionError('Malformed confidence set accepted')
    result = {
        'status': 'PASS', 'created_utc': datetime.now(timezone.utc).isoformat(),
        'python': sys.version, 'elapsed_seconds': time.perf_counter()-start,
        'n': n, 'plane_binary_trees': len(trees), 'distinct_nonempty_tree_unions': len(families),
        **counts,
        'empty_set_is_inconclusive': True, 'conservative_ambiguity_is_inconclusive': True,
        'wrong_singleton_can_produce_wrong_output': True,
        'malformed_candidate_controls_passed': malformed,
        'scope': 'All containing-truth confidence tables for five-taxon circular binary-tree unions; logical contract checks, not statistical calibration or source-network admission.',
        'sha256': {x: hashlib.sha256((HERE/x).read_bytes()).hexdigest()
                   for x in ['sparse_quartet.py', 'abstaining_recovery.py', 'verify_abstaining.py']}
    }
    (HERE/'verification-abstaining.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
