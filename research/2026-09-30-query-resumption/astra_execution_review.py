"""Independent graph truth and all-insertion-order execution of Astra's pinned code.

Does not overwrite author receipts. Quartet answers come from BFS leaf distances;
expected split unions come from separate edge deletion. Finite execution is not
an all-size correctness or complexity proof.
"""
from collections import deque
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib
import json
import math
import platform
import random
import sys
import time

HERE = Path(__file__).resolve().parent
VENDOR = HERE / 'astra-execution-vendor'
if not (VENDOR / 'recover_all.py').is_file():
    VENDOR = HERE.parent / '2026-09-30-astra-exact-query-1156z'
sys.path.insert(0, str(VENDOR))
from adaptive_order import AdaptiveOrderLearner
from recover_all import recover_all, order_bound, reference_provider, sparse_provider
from adaptive_adversary_helpers import trees

PIN = '836cc5a62648f72e59161d583f882b12ac801495'
EXPECTED_BLOBS = {
    'core.py': '2d679d1f284889fb754f2475d6d7c0ec7de47421',
    'adaptive_order.py': '5ac90d944e104d79d893fb266342806e565bfad9',
    'insertion.py': '88c0b7dd1027d48ebcce6f6d9382602377f3d462',
    'recover_all.py': '47ce96e814b904400b04f75045f5fd2c8a9c5bc3',
    'order_controls.py': 'fa857d4eb8092c8f060f431213eee550694ee2ef',
    'joint_controls.py': '53aaa3d15235e40ca769dacced15354042d88e78',
    'insertion_controls.py': '97bff880a11d8aff9e0aa56d84bbb468f72e35bc',
    'vendor/sparse_quartet.py': '49933337ce26ce0d5ef58bbfa458bf5706d8e817',
    'vendor/order_recovery.py': 'ec037ceb66d7f68ef0c76842b78b4f751f9f63c6',
}


def verify_blobs():
    for name, expected in EXPECTED_BLOBS.items():
        data = (VENDOR / name).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert actual == expected, (name, actual, expected)
    return EXPECTED_BLOBS


def canon(side, taxa):
    side = frozenset(side)
    other = frozenset(taxa) - side
    return min(side, other, key=lambda s: (len(s), tuple(sorted(s))))


def cut_truth(graph, taxa):
    taxa = frozenset(taxa)
    answer = set()
    for a, neighbors in graph.items():
        for b in neighbors:
            if a >= b:
                continue
            visited = {a}
            queue = [a]
            while queue:
                u = queue.pop()
                for v in graph[u]:
                    if {u, v} == {a, b} or v in visited:
                        continue
                    visited.add(v)
                    queue.append(v)
            side = frozenset(visited) & taxa
            if min(len(side), len(taxa - side)) >= 2:
                answer.add(canon(side, taxa))
    return frozenset(answer)


def bfs_quartet_truth(graph, taxa):
    distances = {}
    for leaf in taxa:
        d = {leaf: 0}
        queue = deque([leaf])
        while queue:
            u = queue.popleft()
            for v in graph[u]:
                if v not in d:
                    d[v] = d[u] + 1
                    queue.append(v)
        assert len(d) == len(graph)
        distances[leaf] = d
    answer = {}
    for q in combinations(sorted(taxa), 4):
        a, b, c, d = q
        sums = [distances[a][b] + distances[c][d],
                distances[a][c] + distances[b][d],
                distances[a][d] + distances[b][c]]
        value = min(sums)
        assert sums.count(value) == 1, (q, sums)
        answer[q] = 1 << sums.index(value)
    return answer


def circles(taxa):
    taxa = sorted(taxa)
    for tail in permutations(taxa[1:]):
        if tail[0] < tail[-1]:
            yield (taxa[0],) + tail


def is_common(ss, order):
    return all(sum((order[i] in s) != (order[(i + 1) % len(order)] in s)
                   for i in range(len(order))) <= 2 for s in ss)


def restricted(ss, taxa):
    taxa = frozenset(taxa)
    return frozenset(canon(s & taxa, taxa) for s in ss
                     if min(len(s & taxa), len(taxa - s)) >= 2)


def checked_run(ss, answers, labels, expected_spaces, row):
    calls = []
    def measured(q):
        assert tuple(sorted(set(q))) == q and len(q) == 4
        calls.append(q)
        return answers[q]
    result = recover_all(labels, measured)
    assert result.expanded_splits() == ss, ('split recovery', labels, ss, result)
    assert is_common(ss, result.order)
    assert len(calls) == len(set(calls)) == result.total_queries
    assert result.total_queries <= math.comb(len(labels), 4)
    assert result.order_queries <= order_bound(len(labels))
    assert result.total_queries <= order_bound(len(labels)) + sparse_provider().query_bound(len(labels), len(ss))
    row['max_order_queries'] = max(row['max_order_queries'], result.order_queries)
    row['max_joint_queries'] = max(row['max_joint_queries'], result.total_queries)
    # A separate run checks the full language after every insertion, not merely
    # the final compatible order returned by joint recovery.
    learner = AdaptiveOrderLearner(labels, lambda q: answers[q])
    def inspect(a):
        taxa = frozenset(a.tree.taxa)
        if taxa not in expected_spaces:
            subsplits = restricted(ss, taxa)
            expected_spaces[taxa] = {c for c in circles(taxa) if is_common(subsplits, c)}
        obtained = a.tree.all_orders()
        assert obtained == expected_spaces[taxa], ('order language', labels, taxa, obtained,
                                                   expected_spaces[taxa], a.history)
        row['order_language_steps_checked'] += 1
    order = learner.run(inspect)
    assert order == result.order
    assert len(learner.cache) == result.order_queries
    assert sum(h['central_nodes'] for h in learner.history) == result.retired_vertices
    row['joint_runs'] += 1
    return result


def small_families():
    rows = []
    for n in (4, 5, 6):
        graphs = trees(n)
        qsets = list(combinations(range(n), 4))
        truth = [(cut_truth(g, range(n)), bfs_quartet_truth(g, range(n))) for g in graphs]
        families = (range(1, 1 << len(graphs)) if n <= 5 else
                    [1 << i for i in range(len(graphs))] +
                    [(1 << i) | (1 << j) for i, j in combinations(range(len(graphs)), 2)])
        unique = {}
        family_count = circular_families = 0
        possible_circles = list(circles(range(n)))
        for family in families:
            family_count += 1
            members = [i for i in range(len(graphs)) if family & (1 << i)]
            ss = frozenset().union(*(truth[i][0] for i in members))
            support = tuple(__import__('functools').reduce(int.__or__,
                            (truth[i][1][q] for i in members), 0) for q in qsets)
            if ss in unique:
                assert unique[ss] == support, 'Split union failed to regenerate BFS support'
            else:
                unique[ss] = support
            if any(is_common(ss, c) for c in possible_circles):
                circular_families += 1
        row = {'n': n, 'tree_graphs': len(graphs), 'families_considered': family_count,
               'circular_families': circular_families, 'distinct_split_unions': len(unique),
               'distinct_circular_targets': 0, 'joint_runs': 0,
               'order_language_steps_checked': 0, 'max_order_queries': 0, 'max_joint_queries': 0}
        for ss, support in unique.items():
            if not any(is_common(ss, c) for c in possible_circles):
                continue
            row['distinct_circular_targets'] += 1
            answers = dict(zip(qsets, support))
            expected_spaces = {}
            insertion_orders = permutations(range(n)) if n <= 5 else (tuple(range(n)), tuple(reversed(range(n))))
            for labels in insertion_orders:
                checked_run(ss, answers, labels, expected_spaces, row)
        rows.append(row)
        print(json.dumps({'completed_small_n': row}), flush=True)
    return rows


def source_switching_truth(fix):
    names = sorted({v for edge in fix['edges'] for v in edge})
    mapping = {name: int(name[1:]) if name.startswith('T') else -1 - i
               for i, name in enumerate(names)}
    base_edges = {frozenset((mapping[a], mapping[b])) for a, b in fix['edges']}
    hybrid_parents = [(mapping[h], tuple(mapping[p] for p in parents))
                      for h, parents in sorted(fix['hybrids'].items())]
    all_ss = set()
    all_answers = {q: 0 for q in combinations(range(5), 4)}
    switching_count = 0
    for choices in product((0, 1), repeat=len(hybrid_parents)):
        edges = set(base_edges)
        for (h, parents), choice in zip(hybrid_parents, choices):
            edges.remove(frozenset((h, parents[1 - choice])))
        graph = {v: set() for v in mapping.values()}
        for a, b in (tuple(e) for e in edges):
            graph[a].add(b)
            graph[b].add(a)
        assert len(edges) == len(graph) - 1
        all_ss.update(cut_truth(graph, range(5)))
        for q, answer in bfs_quartet_truth(graph, range(5)).items():
            all_answers[q] |= answer
        switching_count += 1
    ss = frozenset(all_ss)
    saved_ss = frozenset(canon({int(t[1:]) for t in side}, range(5))
                         for side in fix['displayed_splits']
                         if min(len(side), 5 - len(side)) >= 2)
    assert ss == saved_ss
    for key, pairs in fix['quartets'].items():
        q = tuple(map(int, key))
        saved_answer = 0
        for pair in pairs:
            side = {int(t[1:]) for t in pair}
            if q[0] not in side:
                side = set(q) - side
            saved_answer |= 1 << ({q[0], q[1]}, {q[0], q[2]}, {q[0], q[3]}).index(side)
        assert all_answers[q] == saved_answer
    return ss, all_answers, switching_count


def source_fixtures():
    saved = json.loads((HERE.parent / '2026-09-30-root-exact-query' / 'anchor-collision-receipt.json').read_text())
    rows = []
    for fix in saved['fixtures']:
        ss, answers, switching_count = source_switching_truth(fix)
        row = {'fixture': fix['name'], 'k': len(ss), 'switchings_recomputed': switching_count,
               'joint_runs': 0, 'order_language_steps_checked': 0,
               'max_order_queries': 0, 'max_joint_queries': 0, 'anchor_reference_checks': 0}
        expected_spaces = {}
        references = {a: reference_provider().learn_order(5, lambda q: answers[q], anchor=a) for a in range(5)}
        for labels in permutations(range(5)):
            r = checked_run(ss, answers, labels, expected_spaces, row)
            assert references[labels[0]].independent_orientations == r.internal_vertices
            row['anchor_reference_checks'] += 1
        rows.append(row)
        print(json.dumps({'completed_source': row}), flush=True)
    return rows


def large_graph_cases():
    rng = random.Random(202609301303)
    rows = []
    for n in (8, 16, 32, 64, 128):
        for kind in ('balanced_tree', 'caterpillar_tree', 'random_tree',
                     'all_adjacent_copies', 'mixed_adjacent_copies'):
            counts = [2 if kind == 'all_adjacent_copies' else
                      rng.randrange(1, 3) if kind == 'mixed_adjacent_copies' else 1
                      for _ in range(n)]
            copies = []
            tip_count = 0
            for count in counts:
                copies.append(tuple(range(tip_count, tip_count + count)))
                tip_count += count
            tips = tuple(range(tip_count))
            def shape(leaves):
                if len(leaves) == 1:
                    return leaves[0]
                cut = len(leaves) // 2 if kind == 'balanced_tree' else rng.randrange(1, len(leaves))
                return (shape(leaves[:cut]), shape(leaves[cut:]))
            if kind == 'caterpillar_tree':
                topology = tips[-1]
                for tip in reversed(tips[:-1]):
                    topology = (tip, topology)
            else:
                topology = shape(tips)
            graph = {}
            next_internal = -1
            def materialize(part):
                nonlocal next_internal
                if type(part) is int:
                    graph[part] = set()
                    return part
                vertex = next_internal
                next_internal -= 1
                graph[vertex] = set()
                for child in part:
                    neighbor = materialize(child)
                    graph[vertex].add(neighbor)
                    graph[neighbor].add(vertex)
                return vertex
            materialize(topology)
            distances = {}
            for leaf in tips:
                d = {leaf: 0}
                queue = deque([leaf])
                while queue:
                    u = queue.popleft()
                    for v in graph[u]:
                        if v not in d:
                            d[v] = d[u] + 1
                            queue.append(v)
                distances[leaf] = d
            raw_splits = cut_truth(graph, tips)
            expected = set()
            max_variable = 0
            for side in raw_splits:
                fixed = {x for x, occurrence in enumerate(copies) if set(occurrence) <= side}
                variable = [x for x, occurrence in enumerate(copies)
                            if set(occurrence) & side and not set(occurrence) <= side]
                assert len(variable) <= 2
                max_variable = max(max_variable, len(variable))
                for flags in product((0, 1), repeat=len(variable)):
                    selected = fixed | {x for x, flag in zip(variable, flags) if flag}
                    if min(len(selected), n - len(selected)) >= 2:
                        expected.add(canon(selected, range(n)))
            expected = frozenset(expected)
            assert is_common(expected, tuple(range(n)))
            label_map = {x: 3 * x + 7 for x in range(n)}
            reverse_labels = {v: k for k, v in label_map.items()}
            target = frozenset(frozenset(label_map[x] for x in s) for s in expected)
            labels = list(label_map.values())
            rng.shuffle(labels)
            actual_calls = []
            def oracle(q):
                actual_calls.append(q)
                logical = [reverse_labels[x] for x in q]
                answer = 0
                for a, b, c, d in product(*(copies[x] for x in logical)):
                    sums = [distances[a][b] + distances[c][d],
                            distances[a][c] + distances[b][d],
                            distances[a][d] + distances[b][c]]
                    least = min(sums)
                    assert sums.count(least) == 1
                    answer |= 1 << sums.index(least)
                assert answer in (1, 2, 3, 4, 5, 6)
                return answer
            result = recover_all(tuple(labels), oracle)
            assert result.expanded_splits() == target
            assert is_common(target, result.order)
            assert len(actual_calls) == len(set(actual_calls)) == result.total_queries
            assert result.order_queries <= order_bound(n)
            assert result.total_queries <= order_bound(n) + sparse_provider().query_bound(n, len(target))
            rows.append({'n': n, 'kind': kind, 'physical_tips': tip_count,
                         'k': len(target), 'noncontiguous_labels': True,
                         'order_queries': result.order_queries,
                         'joint_queries': result.total_queries,
                         'max_variable_copy_labels_per_physical_split': max_variable})
        print(json.dumps({'completed_large_n': n, 'cases': 5,
                          'max_joint_queries': max(r['joint_queries'] for r in rows if r['n'] == n)}), flush=True)
    return rows


def run():
    began = time.monotonic()
    report = {'status': 'RUNNING', 'pinned_commit': PIN, 'python': platform.python_version(),
              'verified_python_blobs': verify_blobs(),
              'small_families': small_families(), 'source_fixtures': source_fixtures(),
              'larger_graph_cases': large_graph_cases()}
    report.update(status='PASS', elapsed_seconds=time.monotonic() - began,
                  scope='Independent finite execution with BFS oracle and graph-cut truth. Full small-family enumeration at n4/n5, singleton/pair families n6. Equivalent targets deduplicated. All insertion orders n4/n5; forward/reverse n6. Source graph admission remains inherited; switching answers and split union recomputed independently. Larger adjacent-copy families are graph-derived generic tree families, not certified source networks. Not an all-size proof, novelty claim or biological validation.')
    return report


if __name__ == '__main__':
    destination = HERE / 'astra-execution-review-checks.json'
    try:
        report = run()
    except Exception as exc:
        destination.write_text(json.dumps({'status': 'FAIL', 'pinned_commit': PIN,
                                          'error': repr(exc)}, indent=2) + '\n')
        raise
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
