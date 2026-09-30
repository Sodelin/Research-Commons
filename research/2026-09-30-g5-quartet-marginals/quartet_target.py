"""Target decoding from complete rooted calendar-quartet law interfaces.

The law interface promises valid observable calendar covers and exact local
right-germ derivatives on every selected marginal queried. This module never
inspects a source graph or inheritance mode. It does not validate membership of
an arbitrary proposed law in the biological source class. Resource exhaustion
and missing data raise Unknown, not a completeness certificate.
"""
from __future__ import annotations
from itertools import combinations
from typing import Callable, Iterable, Mapping
from metric_partition_inverse import (
    Unknown, canonical, chronological_clusters, recover_occupancy,
    splits_from_clusters, quartets_from_splits,
)


def normalize_quartets(labels: Iterable[str], table: Mapping) -> dict:
    labels = tuple(sorted(labels))
    if len(labels) < 4 or len(set(labels)) != len(labels):
        raise ValueError('At least four distinct labels are required')
    expected = set(combinations(labels, 4))
    if set(table) != expected:
        raise ValueError('The complete four-subset table is required')
    result = {}
    for A in sorted(expected):
        masks = set()
        for q in table[A]:
            q = canonical(q)
            if len(q) != 2 or any(len(b) != 2 for b in q):
                raise ValueError('Not a resolved quartet')
            if tuple(sorted(q[0] + q[1])) != A:
                raise ValueError('Quartet labels differ from its subset')
            masks.add(q)
        if not masks:
            raise ValueError('Empty complete support for a binary displayed family')
        result[A] = masks
    return result


def find_common_circle(labels: Iterable[str], table: Mapping,
                       max_search_nodes: int = 2_000_000):
    """Find one compatible circle by exact finite backtracking.

This intentionally simple reference may take factorial time. It searches
orders of the GIVEN target table, not source graphs or optimal query policies.
The first label fixes rotation; orientation need not be fixed for correctness.
"""
    labels = tuple(sorted(labels))
    table = normalize_quartets(labels, table)
    nodes = 0

    def extend(prefix, remaining):
        nonlocal nodes
        nodes += 1
        if nodes > max_search_nodes:
            raise Unknown('Reference circular-order search budget exhausted')
        if not remaining:
            return prefix
        for x in remaining:
            # The old triple appears in its final relative order. Its alternating
            # quartet with the appended x may not be a displayed resolution.
            if any(canonical(((a, c), (b, x))) in table[tuple(sorted((a, b, c, x)))]
                   for a, b, c in combinations(prefix, 3)):
                continue
            got = extend(prefix + (x,), tuple(y for y in remaining if y != x))
            if got is not None:
                return got
        return None

    order = extend((labels[0],), labels[1:])
    if order is None:
        raise ValueError('No circular order is compatible with the support table')
    return order, {'order_search_nodes': nodes,
                   'order_search_cost': 'factorial worst-case reference; not optimal-query enumeration'}


def boundary_splits(order, table):
    """Recover the union of displayed nontrivial splits using boundary quartets."""
    order = tuple(order)
    labels = tuple(sorted(order))
    table = normalize_quartets(labels, table)
    n = len(order)
    result = set()
    queries = 0
    # i and j designate the two cut gaps immediately after their entries.
    for i in range(n):
        for j in range(i + 1, n):
            block = order[i + 1:j + 1]
            if len(block) < 2 or n - len(block) < 2:
                continue
            a, b, c, d = order[i], order[(i + 1) % n], order[j], order[(j + 1) % n]
            q = canonical(((b, c), (a, d)))
            queries += 1
            if q in table[tuple(sorted((a, b, c, d)))]:
                result.add(canonical((block, tuple(x for x in order if x not in block))))
    return result, {'boundary_membership_checks': queries}


def decode_quartet_marginals(labels: Iterable[str], calendar_cells: Iterable,
                             germ: Callable, max_atoms: int = 100,
                             max_derivative: int = 1000):
    """Use local derivatives supplied by each four-tip marginal and its marginals.

'germ(selected, t, k)' returns the kth local derivative as a partition:weight
mapping. A common valid calendar cover is promised; redundant cells are legal.
Return Q, S, one compatible order, and exact algebra/stage certificates.
"""
    labels = tuple(sorted(labels))
    cells = tuple(calendar_cells)
    local = {}
    certificates = []

    def support(selected, t):
        selected = tuple(sorted(selected))
        key = (selected, t)
        if len(selected) > 4:
            raise ValueError('Only four-tip and smaller marginal calls are permitted')
        if key not in local:
            answer, cert = recover_occupancy(
                selected, lambda k: germ(selected, t, k),
                max_atoms=max_atoms, max_derivative=max_derivative)
            local[key] = answer
            certificates.append({'selected': selected, 'time': t, 'algebra': cert})
        return local[key]

    Q = {}
    runs = []
    for A in combinations(labels, 4):
        clusters, stages = chronological_clusters(A, cells, support)
        small_splits = splits_from_clusters(A, clusters)
        Q[A] = quartets_from_splits(A, small_splits)[A]
        runs.append({'subset': A, 'clusters': sorted(map(sorted, clusters)), 'stages': stages})
    order, order_checks = find_common_circle(labels, Q)
    S, boundary_checks = boundary_splits(order, Q)
    return Q, S, order, {'local_certificates': certificates, 'quartet_runs': runs,
                        **order_checks, **boundary_checks}
