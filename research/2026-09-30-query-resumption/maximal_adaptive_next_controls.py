"""Independent rank and admitted leaf-extension controls.

The rank control Gaussian-eliminates full anchored quartet rows from
graph-generated trees. It does not call the adaptive implementation.
The source-extension check reuses the inherited actual admission receipt.
"""
from itertools import combinations, permutations
from functools import lru_cache
from pathlib import Path
import importlib.util
import json


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / '2026-09-30-root-exact-query/verify_candidate_order.py'
spec = importlib.util.spec_from_file_location('independent_rank_trees', SOURCE)
graph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(graph)


def support(splits, q):
    a, b, c, d = q
    full = sum(1 << x for x in q)
    result = 0
    for side in splits:
        part = side & full
        if part.bit_count() != 2:
            continue
        for i, partner in enumerate((b, c, d)):
            pair = (1 << a) | (1 << partner)
            if part in (pair, full ^ pair):
                result |= 1 << i
    return result


def primitive_row(triple, mask, index):
    x, y, z = triple
    choices = ((index[(x, y)], index[(x, z)]),
               (index[(x, y)], index[(y, z)]),
               (index[(x, z)], index[(y, z)]))
    return [(1 << a) | (1 << b) for bit, (a, b) in enumerate(choices)
            if mask & (1 << bit)]


def rank(rows):
    basis = {}
    for row in rows:
        while row:
            leading = row.bit_length() - 1
            if leading not in basis:
                basis[leading] = row
                break
            row ^= basis[leading]
    return len(basis)


def canonical_circle(order, anchor):
    i = order.index(anchor)
    order = order[i:] + order[:i]
    return order if order[1] < order[-1] else (order[0],) + order[:0:-1]


def profile_minimax(profiles, quartets):
    """Exact recurrence for identifying distinct full split/support outputs."""
    profiles = sorted(profiles)
    groups = []
    for qi in range(len(quartets)):
        groups.append({answer: sum(1 << i for i, p in enumerate(profiles)
                                   if p[qi] == answer)
                       for answer in set(p[qi] for p in profiles)})

    @lru_cache(None)
    def depth(state):
        if state.bit_count() <= 1:
            return 0
        choices = []
        for outcomes in groups:
            children = [state & child for child in outcomes.values() if state & child]
            if len(children) >= 2:
                choices.append(1 + max(depth(child) for child in children))
        assert choices
        return min(choices)

    answer = depth((1 << len(profiles)) - 1)
    return {'support_profiles': len(profiles), 'optimal_worst_case_queries': answer,
            'memoized_candidate_states': depth.cache_info().currsize}


def exact_family_minimax(n):
    """Exhaustively solve the finite broader tree-family decision-tree problem."""
    quartets = list(combinations(range(n), 4))
    split_sets = [graph.graph_splits(t, n) for t in graph.trees(n)]
    tree_profiles = [tuple(support(s, q) for q in quartets) for s in split_sets]
    profiles = set()
    for tail in permutations(range(1, n)):
        if tail[0] > tail[-1]:
            continue
        circle = (0,) + tail
        compatible = [i for i, ss in enumerate(split_sets)
                      if all(graph.is_circular(s, circle) for s in ss)]
        for family in range(1, 1 << len(compatible)):
            profile = [0] * len(quartets)
            for j, t in enumerate(compatible):
                if family & (1 << j):
                    for qi, value in enumerate(tree_profiles[t]):
                        profile[qi] |= value
            profiles.add(tuple(profile))
    return {'n': n, **profile_minimax(profiles, quartets),
            'scope': 'All nonempty common-circle binary-tree families; not an admitted-network minimax result.'}


def admitted_fixture_minimax(saved):
    n = 5
    full = (1 << n) - 1
    quartets = list(combinations(range(n), 4))
    profiles = {tuple(support(graph.graph_splits(t, n), q) for q in quartets)
                for t in graph.trees(n)}
    input_counts = {'singleton_trees': len(profiles)}
    fixture_splits = {}
    for fixture in saved['fixtures']:
        original = {sum(1 << int(x[1:]) for x in side)
                    for side in fixture['displayed_splits']}
        original = {s for s in original if min(s.bit_count(), n - s.bit_count()) >= 2}
        fixture_splits[fixture['name']] = {min(s, full ^ s) for s in original}
        orbit = set()
        for relabel in permutations(range(n)):
            splits = {min(sum(1 << relabel[i] for i in range(n) if s & (1 << i)),
                          full ^ sum(1 << relabel[i] for i in range(n) if s & (1 << i)))
                      for s in original}
            orbit.add(tuple(support(splits, q) for q in quartets))
        input_counts[fixture['name'] + '_orbit_profiles'] = len(orbit)
        profiles.update(orbit)
    baseline = tuple(support(fixture_splits['N2'], q) for q in quartets)
    witnesses = []
    tiny_profiles = {baseline}
    for rotation in range(n):
        def moved(s):
            return sum(1 << ((i + rotation) % n) for i in range(n) if s & (1 << i))
        n1 = {min(moved(s), full ^ moved(s)) for s in fixture_splits['N1']}
        n2 = {min(moved(s), full ^ moved(s)) for s in fixture_splits['N2']}
        assert n2 == fixture_splits['N2']
        profile = tuple(support(n1, q) for q in quartets)
        different = [q for q, x, y in zip(quartets, baseline, profile) if x != y]
        assert different == [tuple(i for i in range(n) if i != rotation)]
        assert n1 != fixture_splits['N2']
        witnesses.append({'rotation': rotation, 'only_different_quartet': different[0],
                          'missing_split_as_mask': next(iter(fixture_splits['N2'] - n1))})
        tiny_profiles.add(profile)
    assert profile_minimax(tiny_profiles, quartets)['optimal_worst_case_queries'] == 5
    return {'n': n, 'input_orbits': input_counts, **profile_minimax(profiles, quartets),
            'explicit_five_query_adversary': {'baseline': 'N2', 'alternatives': witnesses,
                                             'distinct_profiles': len(tiny_profiles)},
            'scope': 'Source-admitted subset: all labeled binary trees and all relabelings of actual graph-certified N1/N2. Its optimum lower-bounds the full admitted source optimum.'}


def run():
    records = []
    tree_count = 0
    for n in range(4, 8):
        pairs = list(combinations(range(1, n), 2))
        index = {pair: i for i, pair in enumerate(pairs)}
        ranks = set()
        for tree in graph.trees(n):
            splits = graph.graph_splits(tree, n)
            rows = []
            for triple in combinations(range(1, n), 3):
                mask = support(splits, (0,) + triple)
                assert mask in (1, 2, 4)
                rows.extend(primitive_row(triple, mask, index))
            value = rank(rows)
            assert value == (n - 2) * (n - 3) // 2
            ranks.add(value)
            tree_count += 1
        records.append({'n': n, 'binary_trees': len(graph.trees(n)),
                        'pair_variables': len(pairs), 'full_primitive_ranks': sorted(ranks),
                        'common_order_dimension': n - 2})

    saved = json.loads((HERE.parent / (
        '2026-09-30-root-exact-query/anchor-collision-receipt.json')).read_text())
    fixture = next(f for f in saved['fixtures'] if f['name'] == 'N1')
    n = 5
    full = (1 << n) - 1
    splits = {min(sum(1 << int(x[1:]) for x in side),
                  full ^ sum(1 << int(x[1:]) for x in side))
              for side in fixture['displayed_splits']}
    splits = {s for s in splits if min(s.bit_count(), n - s.bit_count()) >= 2}
    assert splits == {3, 6, 7, 14}
    full_orders = [(0,) + tail for tail in permutations(range(1, n))
                   if tail[0] < tail[-1] and
                   all(graph.is_circular(s, (0,) + tail) for s in splits)]
    assert full_orders == [(0, 1, 2, 3, 4)]
    retained = 30
    restricted = {s & retained for s in splits if 0 < (s & retained) < retained}
    old_orders = [(1,) + tail for tail in permutations((2, 3, 4))
                  if tail[0] < tail[-1] and
                  all(graph.is_circular(s, (1,) + tail) for s in restricted)]
    assert old_orders == [(1, 2, 3, 4), (1, 2, 4, 3)]
    old = (1, 2, 4, 3)
    insertions = {canonical_circle(old[:i] + (0,) + old[i:], 0)
                  for i in range(len(old))}
    assert len(insertions) == 4
    passing = [o for o in insertions if all(graph.is_circular(s, o) for s in splits)]
    assert passing == []
    return {'status': 'PASS', 'tree_rank_controls': records,
            'total_binary_tree_rank_controls': tree_count,
            'broader_family_exact_minimax': [exact_family_minimax(n) for n in (4, 5)],
            'admitted_fixture_subset_exact_minimax': admitted_fixture_minimax(saved),
            'source_extension_counterexample': {'fixture': 'N1',
                'admission_receipt_reused': True, 'full_splits_as_masks': sorted(splits),
                'deleted_taxon': 0, 'restricted_common_orders': old_orders,
                'full_common_orders': full_orders, 'nonextendible_old_circle': old,
                'tested_insertions': sorted(insertions), 'passing_insertions': passing},
            'scope': 'Finite Gaussian rank controls and an actual admitted source-order extension counterexample. No master adaptive lower bound.'}


if __name__ == '__main__':
    result = run()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
