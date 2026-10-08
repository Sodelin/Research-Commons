#!/usr/bin/env python3
"""Exact source-definition enumeration, not a native binary or Lean replay.

Four old A roots traverse one Kingman edge; then B enters and the original
ancestral Kingman completion is executed. Outside C,D are forgotten only by
the inherited source pruning/projectivity theorem. All arithmetic is rational.
"""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
import hashlib
import json
from pathlib import Path


def canon(forest):
    return tuple(sorted(forest, key=repr))


def merge(a, b):
    return tuple(sorted((a, b), key=repr))


def next_forests(forest):
    n = len(forest)
    for i, j in combinations(range(n), 2):
        yield canon(tuple(forest[k] for k in range(n) if k not in (i, j))
                    + (merge(forest[i], forest[j]),)), Q(2, n * (n - 1))


def prefix_distributions():
    states = {canon(("A1", "A2", "A3", "A4")): Q(1)}
    out = {4: states}
    for k in (3, 2, 1):
        nxt = defaultdict(Q)
        for forest, p in states.items():
            for dest, w in next_forests(forest):
                nxt[dest] += p * w
        states = dict(nxt)
        out[k] = states
    return out


@lru_cache(None)
def completion(forest):
    if len(forest) == 1:
        return ((forest[0], Q(1)),)
    out = defaultdict(Q)
    for dest, p in next_forests(forest):
        for tree, w in completion(dest):
            out[tree] += p * w
    return tuple(out.items())


def counts(x):
    # The actual pure-death holding rates are 6,3,1; these are their exact rows.
    return {4: x**6, 3: 2*(x**3-x**6),
            2: Q(9, 5)*x-3*x**3+Q(6, 5)*x**6,
            1: 1-Q(9, 5)*x+x**3-Q(1, 5)*x**6}


def full_law(x, prefixes):
    out = defaultdict(Q)
    for k, pk in counts(x).items():
        for forest, p in prefixes[k].items():
            for tree, w in completion(canon(forest+("B",))):
                out[tree] += pk*p*w
    return dict(out)


def prune(tree, keep):
    if isinstance(tree, str):
        return tree if tree in keep else None
    a, b = (prune(t, keep) for t in tree)
    if a is None:
        return b
    if b is None:
        return a
    return merge(a, b)


def leaves(tree):
    if isinstance(tree, str):
        return frozenset((tree,))
    return leaves(tree[0]) | leaves(tree[1])


def has_clade(tree, wanted):
    if leaves(tree) == wanted:
        return True
    return not isinstance(tree, str) and any(has_clade(t, wanted) for t in tree)


def indicator(tree, k):
    wanted = frozenset("A"+str(i) for i in range(1, k+1))
    return int(has_clade(prune(tree, wanted | {"B"}), wanted))


def cubic_channel(tree):
    return Q(1, 2)+(Q(291,64)-Q(1971,64)*indicator(tree,2)
                      +Q(225,4)*indicator(tree,3)-30*indicator(tree,4))/512


def fold_channel(tree):
    return Q(1,2)+(Q(15,8)-Q(63,8)*indicator(tree,2)
                      +6*indicator(tree,3))/64


def cubic(x):
    return Q(1,2)+(x**6-Q(5,8)*x**3+Q(9,32)*x)/512


def fold(x):
    return Q(1,2)+(x**3-Q(3,4)*x)/64


def wire(q):
    return f"{q.numerator}/{q.denominator}"


def main():
    checks = 0
    def require(condition):
        nonlocal checks
        if not condition:
            raise AssertionError(f"failed exact check {checks+1}")
        checks += 1

    prefixes = prefix_distributions()
    for row in prefixes.values():
        require(sum(row.values()) == 1)
    xs = sorted({Q(i,j) for j in range(2,13) for i in range(1,j)})
    target = Q(16389,32768)
    fold_target = Q(127,256)
    trees = set()
    for x in xs:
        cs = counts(x)
        require(sum(cs.values()) == 1)
        require(all(v > 0 for v in cs.values()))
        law = full_law(x,prefixes)
        trees.update(law)
        require(sum(law.values()) == 1)
        require(all(p > 0 for p in law.values()))
        formulas = {2:1-Q(2,3)*x,3:1-x+x**3/6,
                    4:1-Q(6,5)*x+x**3/3-x**6/30}
        for k in (2,3,4):
            require(sum(p*indicator(t,k) for t,p in law.items()) == formulas[k])
        require(sum(p*cubic_channel(t) for t,p in law.items()) == cubic(x))
        require(sum(p*fold_channel(t) for t,p in law.items()) == fold(x))
        require(cubic(x)-target == (2*x-1)**3*(8*x**3+12*x**2+12*x+5)/32768)
        require(fold(x)-fold_target == (x-Q(1,2))**2*(x+1)/64)
        # The actual entire one-parameter response derivative factorization.
        require(6*x**5-Q(15,8)*x*x+Q(9,32)
                == 6*(x-Q(1,2))**2*(x**3+x*x+Q(3,4)*x+Q(3,16)))
    require(len(trees)==105)
    for tree in trees:
        require(0 < cubic_channel(tree) < 1)
        require(0 < fold_channel(tree) < 1)
    require(cubic(Q(1,2)) == target)
    require(fold(Q(1,2)) == fold_target)
    require(cubic(Q(1,4)) < target < cubic(Q(3,4)))
    require(fold(Q(1,4)) > fold_target and fold(Q(3,4)) > fold_target)
    require(6*Q(1,2)**5-Q(15,8)*Q(1,2)**2+Q(9,32) == 0)
    require(30*Q(1,2)**4-Q(15,4)*Q(1,2) == 0)
    require(120*Q(1,2)**3-Q(15,4) == Q(45,4))
    receipt = {
        "status":"PASS", "exact_checks":checks, "rational_edge_values":len(xs),
        "complete_selected_labelled_topologies":len(trees),
        "source":"one ordinary A edge, 4 current A roots, B singleton, ancestral completion",
        "full_original_sample_allocation":{"A":4,"B":1,"C":1,"D":1},
        "outside_forgetting":"inherited original source pruning/projectivity, not independently executed here",
        "cubic_target":wire(target),"fold_target":wire(fold_target),
        "cubic_channel_range":[wire(min(map(cubic_channel,trees))),wire(max(map(cubic_channel,trees)))],
        "fold_channel_range":[wire(min(map(fold_channel,trees))),wire(max(map(fold_channel,trees)))],
        "cubic_face_residuals":[wire(cubic(Q(1,4))-target),wire(cubic(Q(3,4))-target)],
        "fold_face_residuals":[wire(fold(Q(1,4))-fold_target),wire(fold(Q(3,4))-fold_target)],
        "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "evidence":"exact source-definition enumeration; no native binary, Lean, compiler, QE, or API execution",
    }
    Path(__file__).with_name("degree-source-test-receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2))


if __name__ == "__main__":
    main()
