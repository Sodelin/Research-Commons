"""Finite checks for the master-facing supplement; not a full NMSC simulator."""
from fractions import Fraction as F
from itertools import combinations
from math import ceil, exp, log
from pathlib import Path
import hashlib
import json


def rooted_trees(labels):
    labels = frozenset(labels)
    if len(labels) == 1:
        return [next(iter(labels))]
    first = min(labels)
    rest = sorted(labels - {first})
    result = []
    for size in range(len(rest)):
        for subset in combinations(rest, size):
            left = frozenset(subset) | {first}
            right = labels - left
            for a in rooted_trees(left):
                for b in rooted_trees(right):
                    result.append((a, b))
    return result


def clusters(tree):
    if isinstance(tree, str):
        return frozenset(tree), {frozenset(tree)}
    a, ac = clusters(tree[0])
    b, bc = clusters(tree[1])
    return a | b, ac | bc | {a | b}


def run():
    trees = rooted_trees('ABCD')
    assert len(trees) == 15
    for t in trees:
        _, cs = clusters(t)
        assert not ({frozenset('ABC'), frozenset('ACD')} <= cs)
    dominance_checks = 0
    for i in range(1, 32):
        x = F(i, 32)
        f3 = 1 - F(3, 2)*x + x**3/2
        f2 = 1 - x
        assert 0 < f3 <= f2 <= 1
        dominance_checks += 1
    x = F(1, 4)
    f3 = 1 - F(3, 2)*x + x**3/2
    margin = f3 - F(1, 2)
    assert f3 == F(81, 128) and margin == F(17, 128)
    delta = .05
    m = ceil(log(1/delta)/(2*float(margin)**2))
    assert exp(-2*m*float(margin)**2) <= delta
    # A finite abstract full-law confidence-set test. Repeated laws with
    # different target labels deliberately encode nonidentifiability.
    models = [('A',(F(1,3),)*3), ('B',(F(1,3),)*3),
              ('C',(F(3,4),F(1,8),F(1,8))),
              ('D',(F(1,8),F(1,8),F(3,4)))]
    radius = F(1,10)
    checked = unique = ambiguous = 0
    dist = lambda p,q: max(abs(a-b) for a,b in zip(p,q))
    for label,p in models:
        sep = min(dist(p,q) for other,q in models if other != label)
        for size in range(1,16):
            for a in range(size+1):
                for b in range(size-a+1):
                    phat = (F(a,size),F(b,size),F(size-a-b,size))
                    if dist(phat,p) > radius:
                        continue
                    candidates = {s for s,q in models if dist(phat,q) <= radius}
                    assert label in candidates
                    if sep > 2*radius:
                        assert candidates == {label}
                    if len(candidates) == 1:
                        unique += 1
                    else:
                        ambiguous += 1
                    checked += 1
    report = {'session':'ASTRA-STAT-20260930-0942Z',
              'scope':'finite arithmetic/cluster/confidence-set checks; not full-model likelihood enumeration',
              'rooted_four_taxon_topologies_checked':len(trees),
              'three_lineage_dominance_checks':dominance_checks,
              'original_root_bit_probability_lower':str(f3),
              'relabeled_root_bit_probability_upper':str(1-f3),
              'threshold_margin':str(margin), 'risk':delta, 'loci_sufficient':m,
              'hoeffding_error_upper':exp(-2*m*float(margin)**2),
              'abstract_confidence_events_checked':checked,
              'unique_events':unique,'ambiguous_events':ambiguous,
              'verification_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name('master-verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O')
    run()
