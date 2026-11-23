"""Exact, partial G3 NO screen for an observable natural disjoint-quartet event."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations
import json

# A balanced rooted quartet has a 2+2 root split, as opposed to 1+3.
def balanced(tree):
    return isinstance(tree[0], tuple) and isinstance(tree[1], tuple)

def restrict(tree, keep):
    if isinstance(tree, int):
        return tree if tree in keep else None
    x, y = (restrict(a, keep) for a in tree)
    return y if x is None else x if y is None else (x, y)

def insert(tree, leaf):
    """Insert the new leaf on each edge, treating the root stem as an edge."""
    yield (tree, leaf)
    if isinstance(tree, tuple):
        left, right = tree
        yield from ((new, right) for new in insert(left, leaf))
        yield from ((left, new) for new in insert(right, leaf))

def all_trees(n):
    if n == 1:
        yield 0
    else:
        for t in all_trees(n-1):
            yield from insert(t, n-1)

def canonical(tree):
    if isinstance(tree, int):
        return tree
    return tuple(sorted(map(canonical, tree), key=repr))

def block_event(tree, a, b):
    return int(balanced(restrict(tree, a))), int(balanced(restrict(tree, b)))

def check_no(masses):
    """Check four exact masses keyed by (X1,X2). Invalid input raises ValueError.

    Only applicable when each Xj is the same permutation-invariant event
    applied to one disjoint four-copy restriction of the same NATURAL row.
    'UNKNOWN' never certifies source feasibility.
    """
    keys = {(0,0),(1,0),(0,1),(1,1)}
    if set(masses) != keys:
        raise ValueError("need exactly four event masses")
    if any(type(v) not in (Q, int, str) for v in masses.values()):
        raise ValueError("need exact rationals, not floating-point data")
    a,b,c,d = (Q(masses[k]) for k in ((0,0),(1,0),(0,1),(1,1)))
    if min(a,b,c,d)<0 or a+b+c+d != 1 or b != c:
        raise ValueError("not a normalized, block-symmetric event law")
    p, q = b+d, d
    gap = q-p*p
    if gap >= 0:
        return {"decision":"UNKNOWN","p":str(p),"q":str(q)}
    n = (p*(1-p)) // (-gap) + 2
    var = n*p*(1-p)+n*(n-1)*gap
    assert var < 0
    return dict(decision="NO",p=str(p),q=str(q),covariance=str(gap),
                hypothetical_blocks=n,hypothetical_copies=4*n,
                forced_negative_variance=str(var))

def fixture():
    block0, block1 = frozenset(range(4)), frozenset(range(4,8))
    shape = ((0,(1,2)),(3,(4,(5,(6,7)))))
    universe = set(range(8))
    expected = Counter(block_event(shape, a, universe-set(a)) for a in combinations(range(8),4))
    assert expected == {(0,0):10,(1,0):30,(0,1):30}
    labels = Counter()
    for perm in permutations(range(8)):
        def permute(t):
            return perm[t] if isinstance(t, int) else tuple(map(permute, t))
        labels[canonical(permute(shape))] += 1
    assert sum(labels.values()) == 40320
    all_labelled = {canonical(t) for t in all_trees(8)}
    assert all_labelled >= set(labels) and len(all_labelled) == 135135
    keys = ((0,0),(1,0),(0,1),(1,1))
    uniform, fixed = Counter(), Counter()
    for t in all_labelled:
        k = block_event(t, block0, block1)
        uniform[k] += 1
        fixed[k] += labels.get(t, 0)
    assert uniform == {(0,0):87408,(1,0):20700,(0,1):20700,(1,1):6327}
    assert all(fixed[k] == expected[k]*576 for k in keys)
    # Uniform admixture gives all 135,135 topologies positive mass.
    law = {k: Q(7,12)*Q(fixed[k],40320)+Q(5,12)*Q(uniform[k],135135) for k in keys}
    assert law[(1,0)]+law[(1,1)] == Q(1,3)
    assert law[(1,1)] == Q(703,36036)
    saw = check_no(law)
    assert saw["decision"] == "NO" and saw["hypothetical_blocks"] == 4
    assert check_no({(0,0):Q(4,9),(1,0):Q(2,9),(0,1):Q(2,9),(1,1):Q(1,9)})["decision"]=="UNKNOWN"
    return {"fixture":{str(k):str(v) for k,v in law.items()},
            "counts_fixed":{str(k):fixed[k] for k in keys},
            "counts_uniform":{str(k):uniform[k] for k in keys}, "result":saw}

if __name__ == "__main__":
    print(json.dumps(fixture(), indent=2))
