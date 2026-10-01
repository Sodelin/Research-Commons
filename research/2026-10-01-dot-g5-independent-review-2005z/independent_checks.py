"""Independent bounded controls for the G5 hand-proof review.

No G5 author code is imported. These checks corroborate, and do not prove,
the unbounded theorem. Standard library only; exact Fraction arithmetic.
"""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from functools import lru_cache
import hashlib
import json
import platform
from pathlib import Path


def canon(blocks):
    return tuple(sorted(tuple(sorted(b)) for b in blocks))


@lru_cache(None)
def partitions(xs):
    if not xs:
        return ((),)
    x, *rest = xs
    answer = set()
    for p in partitions(tuple(rest)):
        answer.add(canon(((x,),) + p))
        for i, b in enumerate(p):
            answer.add(canon(p[:i] + ((x,) + b,) + p[i + 1:]))
    return tuple(sorted(answer))


def frozen_projectors():
    """Project independent frozen coalescents to zero-eigenvalue limit.

    Eigenvalues are read from this separately constructed finite generator,
    not from an author-provided spectral oracle or expected output.
    """
    labels = tuple(range(4))
    count = 0
    coincidences = 0
    for population in partitions(labels):
        for rates in product((F(1), F(2)), repeat=len(population)):
            owner = {x: i for i, b in enumerate(population) for x in b}
            states = [p for p in partitions(labels)
                      if all(len({owner[x] for x in b}) == 1 for b in p)]
            idx = {p: i for i, p in enumerate(states)}
            Q = [[F(0) for _ in states] for _ in states]
            for i, p in enumerate(states):
                for j, k in combinations(range(len(p)), 2):
                    if owner[p[j][0]] != owner[p[k][0]]:
                        continue
                    q = canon([b for a, b in enumerate(p) if a not in (j, k)]
                              + [p[j] + p[k]])
                    r = rates[owner[p[j][0]]]
                    Q[i][idx[q]] += r
                    Q[i][i] -= r
            diagonal = [-Q[i][i] for i in range(len(states)) if Q[i][i]]
            coincidences += int(len(diagonal) != len(set(diagonal)))
            vector = [F(int(p == canon((x,) for x in labels))) for p in states]
            for beta in sorted(set(diagonal)):
                vector = [vector[j] + sum(vector[i] * Q[i][j]
                                         for i in range(len(states))) / beta
                          for j in range(len(states))]
            assert vector == [F(int(p == population)) for p in states]
            count += 1
    return {"frozen_assignments": count,
            "assignments_with_repeated_nonzero_diagonal_rate": coincidences}


@lru_cache(None)
def ordered_trees(xs):
    if len(xs) == 1:
        return (xs[0],)
    return tuple((a, b)
                 for k in range(1, len(xs))
                 for a in ordered_trees(xs[:k])
                 for b in ordered_trees(xs[k:]))


def graph_splits(tree, n):
    """Build an ordinary unrooted graph, then delete every physical edge."""
    graph = {i: set() for i in range(n)}
    next_id = n

    def grow(t):
        nonlocal next_id
        if isinstance(t, int):
            return t
        v = next_id
        next_id += 1
        graph[v] = set()
        for child in t:
            w = grow(child)
            graph[v].add(w)
            graph[w].add(v)
        return v

    top = grow(tree)
    graph[0].add(top)
    graph[top].add(0)
    full = (1 << n) - 1
    out = set()
    for u in graph:
        for v in graph[u]:
            if u > v:
                continue
            reached, todo = set(), [u]
            while todo:
                z = todo.pop()
                if z in reached:
                    continue
                reached.add(z)
                todo.extend(w for w in graph[z]
                            if not ((z == u and w == v) or (z == v and w == u)))
            bit = sum(1 << x for x in reached if x < n)
            if 2 <= bit.bit_count() <= n - 2:
                out.add(min(bit, full ^ bit))
    return out


def quartet_table(splits, n):
    full = (1 << n) - 1
    out = {}
    for a in combinations(range(n), 4):
        mask = sum(1 << x for x in a)
        q = set()
        for s in splits:
            left, right = s & mask, (full ^ s) & mask
            if left.bit_count() == right.bit_count() == 2:
                q.add(min(left, right))
        assert q
        out[mask] = q
    return out


def boundary_decode(order, Q):
    n = len(order)
    full = (1 << n) - 1
    out = set()
    for i in range(n):
        for j in range(i + 2, n):
            block = sum(1 << x for x in order[i + 1:j + 1])
            if block.bit_count() > n - 2:
                continue
            a, b, c, d = order[i], order[(i + 1) % n], order[j], order[(j + 1) % n]
            mask = sum(1 << x for x in (a, b, c, d))
            witness = min((1 << b) | (1 << c), (1 << a) | (1 << d))
            if witness in Q[mask]:
                out.add(min(block, full ^ block))
    return out


def compatible(order, Q):
    for a, b, c, d in combinations(order, 4):
        mask = sum(1 << x for x in (a, b, c, d))
        crossing = min((1 << a) | (1 << c), (1 << b) | (1 << d))
        if crossing in Q[mask]:
            return False
    return True


def circles():
    tree_cases, family_cases, compatible_orders = 0, 0, 0
    for n in range(4, 9):
        family = [graph_splits(t, n) for t in ordered_trees(tuple(range(1, n)))]
        for S in family:
            Q = quartet_table(S, n)
            assert compatible(tuple(range(n)), Q)
            assert boundary_decode(tuple(range(n)), Q) == S
            tree_cases += 1
        # Union preservation follows analytically from each edge witness.
        # These four diverse families independently challenge order choice.
        samples = [family[:1], family[::2], family[-2:], family]
        for subfamily in samples:
            S = set().union(*subfamily)
            Q = quartet_table(S, n)
            assert boundary_decode(tuple(range(n)), Q) == S
            family_cases += 1
            if n <= 7:
                for tail in permutations(range(1, n)):
                    order = (0,) + tail
                    if compatible(order, Q):
                        assert boundary_decode(order, Q) == S
                        compatible_orders += 1
    return {"individual_plane_trees": tree_cases,
            "tree_families": family_cases,
            "compatible_alternative_orders": compatible_orders,
            "maximum_taxa": 8}


AGES = dict(r=12, u=9, v=8, h=5, k=2, a=0, b=0, c=0, d=0)
PARENTS = dict(r=(), u=("r",), v=("r",), h=("u", "v"),
               k=("h",), a=("k",), b=("k",), c=("u",), d=("v",))
TIMES = (0, 2, 5, 8, 9, 12)


def occupancy(labels, t, independent):
    answer = set()
    routes = product((0, 1), repeat=len(labels) if independent else 1)
    for route in routes:
        located = {}
        for i, x in enumerate(labels):
            z = x
            while z != "r":
                parents = PARENTS[z]
                p = parents[(route[i] if independent else route[0]) if z == "h" else 0]
                if AGES[p] > t:
                    break
                z = p
            key = ("ancestor",) if z == "r" else (p, z)
            located.setdefault(key, []).append(x)
        answer.add(canon(located.values()))
    return answer


def chronology(labels, independent):
    groups = {x: {x} for x in labels}
    recorded = {frozenset((x,)) for x in labels}
    for t in TIMES:
        active = tuple(sorted(groups))
        support = occupancy(active, t, independent)
        for p in support:
            for block in p:
                recorded.add(frozenset().union(*(groups[x] for x in block)))
        sure = set.intersection(*(set(p) for p in support))
        for block in sorted(sure):
            if len(block) > 1:
                union = set().union(*(groups.pop(x) for x in block))
                groups[min(block)] = union
    assert len(groups) == 1
    return recorded


def barrier_and_lifting():
    labels = tuple("abcd")
    assert all(AGES[p] > AGES[c] for c in PARENTS for p in PARENTS[c])
    assert all(tuple("ab") in p for p in occupancy(labels, 2, True))
    assert canon((("a", "c"), ("b", "d"))) in occupancy(labels, 9, True)
    assert canon((("a", "d"), ("b", "c"))) in occupancy(labels, 9, True)
    true_clusters = {frozenset(b) for t in TIMES
                     for p in occupancy(labels, t, False) for b in p}
    assert frozenset("ac") not in true_clusters
    assert frozenset("ad") not in true_clusters
    tests = 0
    for k in range(1, 5):
        for chosen in combinations(labels, k):
            expected = {C & set(chosen) for C in true_clusters if C & set(chosen)}
            for independent in (False, True):
                assert chronology(chosen, independent) == expected
                tests += 1
    return {"selected_sample_mechanism_cases": tests,
            "independent_false_partition_controls": 2,
            "source": "positive four-taxon child-bridge diamond with ab cherry",
            "source_admission": "hand checked in REVIEW.md; no all-size census claimed"}


def main():
    result = {"status": "PASS", "python": platform.python_version(),
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "frozen": frozen_projectors(), "circles": circles(),
              "chronology": barrier_and_lifting(),
              "limitations": ["Finite corroboration, not the all-size proof",
                              "No author executable imported or author suite replayed",
                              "No raw-law parser, empirical inference or formal verification"]}
    Path(__file__).with_name("checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
