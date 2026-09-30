#!/usr/bin/env python3
"""Exact universal >=g partial-menu capacity for a bounded row count.

Alphabet codes are 0 -> forced 0, 1 -> random '*', 2 -> forced 1.
A pair pattern is covered iff there is a row with no conflicting forced
choice and at least one of the two coordinates forced.

Enumerates all 3**m column signatures, forms their compatibility graph,
then computes its maximum clique with exact greedy-color branch/bound.
The balanced construction supplies an initial lower bound, but every
search pruning bound comes from an explicit proper graph coloring.
No third-party packages or solvers are used.
"""

from itertools import combinations, product
from math import comb
from time import perf_counter
import argparse
import json


def pair_patterns(x, y):
    """Independent, literal implementation of the operational rule."""
    covered = set()
    for a, b in zip(x, y):
        if a == b == 1:
            continue
        for c, d in product((0, 2), repeat=2):
            if a in (c, 1) and b in (d, 1):
                covered.add((c // 2, d // 2))
    return covered


def compatible(x, y):
    """Equivalent poset criterion; checked against pair_patterns below."""
    return (any(a < b for a, b in zip(x, y))
            and any(a > b for a, b in zip(x, y))
            and any(a + b < 2 for a, b in zip(x, y))
            and any(a + b > 2 for a, b in zip(x, y)))


def central_trinomial(m):
    return sum(comb(m, 2*k) * comb(2*k, k)
               for k in range(m // 2 + 1))


def solve(m):
    started = perf_counter()
    words = list(product(range(3), repeat=m))
    n = len(words)
    adj = [0] * n
    edge_count = 0
    all_patterns = {(0, 0), (0, 1), (1, 0), (1, 1)}
    for i in range(n):
        for j in range(i):
            is_edge = compatible(words[i], words[j])
            assert is_edge == (pair_patterns(words[i], words[j]) == all_patterns)
            if is_edge:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
                edge_count += 1

    # Select one representative from each complement pair in rank m,
    # including the unique fixed point, the all-random signature.
    best = [i for i, x in enumerate(words)
            if sum(x) == m and x <= tuple(2-a for a in x)]
    assert all(compatible(words[i], words[j])
               for i, j in combinations(best, 2))
    initial_lower = len(best)
    nodes = 0
    prunings = 0
    root_color_bound = None

    def color_sort(p):
        vertices, bounds = [], []
        color = 0
        while p:
            color += 1
            q = p
            while q:
                bit = q & -q
                v = bit.bit_length() - 1
                p ^= bit
                q ^= bit
                vertices.append(v)
                bounds.append(color)
                q &= ~adj[v]
        return vertices, bounds

    def expand(clique, p):
        nonlocal best, nodes, prunings, root_color_bound
        nodes += 1
        vertices, bounds = color_sort(p)
        if not clique:
            root_color_bound = bounds[-1] if bounds else 0
        for index in range(len(vertices)-1, -1, -1):
            if len(clique) + bounds[index] <= len(best):
                prunings += 1
                return
            v = vertices[index]
            new = clique + [v]
            q = p & adj[v]
            if q:
                expand(new, q)
            elif len(new) > len(best):
                best = new
            p &= ~(1 << v)

    expand([], (1 << n)-1)
    columns = [words[i] for i in best]
    assert all(pair_patterns(x, y) == all_patterns
               for x, y in combinations(columns, 2))
    rows = [''.join('0*1'[x[t]] for x in columns) for t in range(m)]
    return {
        'rows_m': m,
        'candidate_signatures': n,
        'compatibility_graph_edges': edge_count,
        'maximum_columns_exact': len(best),
        'balanced_initial_lower_bound': initial_lower,
        'root_greedy_coloring_upper_bound': root_color_bound,
        'central_trinomial_T_m': central_trinomial(m),
        'proposed_all_m_formula': (central_trinomial(m)+1)//2,
        'search_nodes': nodes,
        'color_bound_prunings': prunings,
        'witness_rows': rows,
        'witness_columns': [''.join('0*1'[a] for a in x) for x in columns],
        'verified_column_pairs': len(columns)*(len(columns)-1)//2,
        'operational_and_poset_rule_agree_all_candidate_pairs': True,
        'elapsed_seconds': round(perf_counter()-started, 6),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-rows', type=int, default=6)
    parser.add_argument('--output')
    args = parser.parse_args()
    results = [solve(m) for m in range(1, args.max_rows+1)]
    payload = {
        'schema': 'partial-signature-checks/v1',
        'model': 'universal binary pair certificates, >=g coverage, unlimited controls per row',
        'wildcard_semantics': 'random coordinate; ** covers no pair pattern at threshold g',
        'algorithm': 'all ternary signatures + exact bitset max clique with proper greedy-color bounds',
        'scope_caveat': 'generic pair-certificate optimum; no admitted-network lower-bound realization proved here',
        'results': results,
    }
    rendered = json.dumps(payload, indent=2) + '\n'
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as handle:
            handle.write(rendered)
    else:
        print(rendered, end='')


if __name__ == '__main__':
    main()
