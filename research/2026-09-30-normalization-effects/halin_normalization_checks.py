"""Independent finite switching and control checks on source-admitted Halin blobs.

This is exact combinatorics and rational arithmetic. It is not a biological
simulation, general normalization proof, or Lean verification. Source admission
of the explicit plane Halin construction follows the accompanying graph recipe.
"""
from itertools import product, combinations
from functools import lru_cache
from collections import defaultdict, Counter
from fractions import Fraction
from pathlib import Path
import argparse
import json


@lru_cache(None)
def ordered_binary(first, last):
    if last - first == 1:
        return (first,)
    return tuple((left, right) for middle in range(first + 1, last)
                 for left in ordered_binary(first, middle)
                 for right in ordered_binary(middle, last))


def skeleton(shape, d):
    """Unrooted plane binary tree with cyclic leaves U0,...,U(d-1)."""
    edges = []
    count = 0
    def build(t):
        nonlocal count
        if isinstance(t, int):
            return f'U{t}'
        v = f'V{count}'
        count += 1
        for child in t:
            edges.append((v, build(child)))
        return v
    edges.append(('U0', build(shape)))
    assert count == d - 2
    return edges


def adjacency(edges):
    adj = defaultdict(list)
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def component(adj, a, b):
    seen = {b}
    todo = [a]
    while todo:
        v = todo.pop()
        if v in seen:
            continue
        seen.add(v)
        todo.extend(adj[v])
    seen.remove(b)
    return seen


def path(adj, a, b):
    parents = {a: None}
    todo = [a]
    while todo:
        v = todo.pop()
        if v == b:
            break
        for w in adj[v]:
            if w not in parents:
                parents[w] = v
                todo.append(w)
    result = []
    v = b
    while parents[v] is not None:
        result.append(tuple(sorted((v, parents[v]))))
        v = parents[v]
    return result


def fixture(shape, d):
    """Root on one skeleton edge; each outer gap contains a pendant hybrid."""
    original = skeleton(shape, d)
    adj = adjacency(original)
    face_incidence = defaultdict(list)
    for i in range(d):
        for edge in path(adj, f'U{i}', f'U{(i+1)%d}'):
            face_incidence[edge].append(i)
    dual = set()
    edge_rules = []
    for a, b in original:
        faces = face_incidence[tuple(sorted((a, b)))]
        assert len(faces) == 2
        dual.add(tuple(sorted(faces)))
        side = component(adj, a, b)
        base = 0
        crosses = []
        for i in range(d):
            zero = f'U{i}' in side
            one = f'U{(i+1)%d}' in side
            if zero == one:
                if zero:
                    base |= 1 << i
            else:
                crosses.append((i, int(one)))
        assert len(crosses) == 2
        assert tuple(sorted(i for i, value in crosses)) in dual
        edge_rules.append((base, tuple(crosses)))
    rooted = original[1:] + [('R', original[0][0]), ('R', original[0][1])]
    root_adj = adjacency(rooted)
    directed = []
    todo = ['R']
    seen = {'R'}
    while todo:
        v = todo.pop()
        for w in root_adj[v]:
            if w not in seen:
                seen.add(w)
                todo.append(w)
                directed.append((v, w))
    for i in range(d):
        directed += [(f'U{i}', f'H{i}'), (f'U{(i+1)%d}', f'H{i}'),
                     (f'H{i}', f'T{i}')]
    vertices = {v for edge in directed for v in edge}
    for v in vertices:
        degree = (sum(b == v for a, b in directed), sum(a == v for a, b in directed))
        expected = (0, 2) if v == 'R' else (1, 0) if v.startswith('T') else (2, 1) if v.startswith('H') else (1, 2)
        assert degree == expected
    done = set()
    while done != vertices:
        ready = {v for v in vertices-done if all(a in done for a, b in directed if b == v)}
        assert ready, 'Directed graph must be acyclic'
        done |= ready
    # H_i has a single taxon child; its child edge is visibly a cut edge.
    # The plane tree and cyclic leaf arcs give a plane embedding with exterior
    # taxa. Root insertion preserves the embedding and binary degree. Every
    # root-to-leaf path through the U0 side begins through one root child and
    # every path through the remaining skeleton begins through the other, so
    # no non-root vertex is a stable ancestor of all taxa: R is the LSA.
    return original, directed, edge_rules, dual


def canonical_split(mask, d):
    full = (1 << d)-1
    if min(mask.bit_count(), d-mask.bit_count()) < 2:
        return None
    return min(mask, full ^ mask)


def selected_splits(bits, edge_rules, d):
    result = set()
    for base, crosses in edge_rules:
        mask = base
        for i, side_one in crosses:
            if ((bits >> i) & 1) == side_one:
                mask |= 1 << i
        split = canonical_split(mask, d)
        if split is not None:
            result.add(split)
    assert len(result) == max(0, d-3)
    return result


def independent_graph_splits(bits, directed, d):
    edges = []
    for a, b in directed:
        if b.startswith('H'):
            i = int(b[1:])
            chosen_parent = f'U{(i+((bits >> i)&1))%d}'
            if a != chosen_parent:
                continue
        edges.append((a, b))
    adj = adjacency(edges)
    assert len(edges) == len(adj)-1
    result = set()
    for a, b in edges:
        side = component(adj, a, b)
        mask = sum(1 << i for i in range(d) if f'T{i}' in side)
        split = canonical_split(mask, d)
        if split is not None:
            result.add(split)
    return result


def color_dual(d, dual):
    neighbours = [set() for _ in range(d)]
    for i, j in dual:
        neighbours[i].add(j)
        neighbours[j].add(i)
    colors = [-1]*d
    def search():
        if all(c >= 0 for c in colors):
            return True
        unset = [i for i, c in enumerate(colors) if c < 0]
        i = max(unset, key=lambda v: (len({colors[w] for w in neighbours[v] if colors[w]>=0}), len(neighbours[v]), -v))
        for c in range(3):
            if all(colors[w] != c for w in neighbours[i]):
                colors[i] = c
                if search():
                    return True
                colors[i] = -1
        return False
    assert search(), 'The explicit weak dual is three-colourable'
    largest = max(range(3), key=lambda c: (colors.count(c), c))
    other = [c for c in range(3) if c != largest]
    relabel = {other[0]: 0, other[1]: 1, largest: 2}
    colors = tuple(relabel[c] for c in colors)
    assert all(colors[i] != colors[j] for i, j in dual)
    rows = [tuple(0 if c < 2 else None for c in colors),
            tuple(1 if c == 0 else None for c in colors),
            tuple(1 if c == 1 else None for c in colors)]
    assert max(sum(c is not None for c in row) for row in rows) <= (2*d)//3
    return colors, rows


def pair_covered(rows, i, j, a, b):
    return any((row[i] is None or row[i] == a) and (row[j] is None or row[j] == b)
               and (row[i] is not None or row[j] is not None) for row in rows)


def exact_probabilities(records, rows, numerators, denominator):
    result = []
    for row in rows:
        k = row.count(None)
        probs = defaultdict(int)
        total = 0
        for bits, splits in enumerate(records):
            if any(c is not None and ((bits >> i)&1) != c for i, c in enumerate(row)):
                continue
            weight = 1
            for i, c in enumerate(row):
                if c is None:
                    weight *= numerators[i] if ((bits >> i)&1) else denominator-numerators[i]
            total += weight
            for split in splits:
                probs[split] += weight
        assert total == denominator**k
        result.append({split: Fraction(weight, total) for split, weight in probs.items()})
    return result


def quartet_signature(splits, d):
    qs = []
    for q in combinations(range(d), 4):
        found = []
        for split in splits:
            side = tuple(i for i in q if (split >> i)&1)
            if len(side) == 2:
                other = tuple(i for i in q if i not in side)
                found.append(min(side, other))
        assert len(set(found)) == 1
        qs.append(found[0])
    return tuple(qs)


def active_ids(records, d):
    signatures = [quartet_signature(s, d) if d >= 4 else () for s in records]
    active = [i for i in range(d) if any(signatures[x] != signatures[x^(1 << i)]
                                        for x in range(1 << d) if not ((x >> i)&1))]
    # Topology change is equivalent to a changed quartet for binary trees.
    assert active == [i for i in range(d) if any(records[x] != records[x^(1 << i)]
                                                for x in range(1 << d) if not ((x >> i)&1))]
    return active


def two_rows_search(records, support, d):
    """Exact existential two partial rows at fair inheritance, not at all g."""
    support = sorted(support)
    presence = {s: sum(1 << x for x, splits in enumerate(records) if s in splits) for s in support}
    universe = (1 << (1 << d))-1
    literals = {(i, bit): sum(1 << x for x in range(1 << d) if ((x >> i)&1) == bit)
                for i in range(d) for bit in (0, 1)}
    covers = {}
    for row in product((0, None, 1), repeat=d):
        compatible = universe
        for i, bit in enumerate(row):
            if bit is not None:
                compatible &= literals[i, bit]
        denom = 1 << row.count(None)
        cover = sum(1 << j for j, s in enumerate(support) if 2*(presence[s]&compatible).bit_count() >= denom)
        covers.setdefault(cover, row)
    full = (1 << len(support))-1
    masks = list(covers)
    for a in masks:
        missing = full ^ a
        for b in masks:
            if b & missing == missing:
                return {'feasible': True, 'rows': [list(covers[a]), list(covers[b])],
                        'unique_cover_masks': len(masks), 'candidate_rows': 3**d}
    return {'feasible': False, 'unique_cover_masks': len(masks), 'candidate_rows': 3**d}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-ports', type=int, default=8)
    parser.add_argument('--two-row-through', type=int, default=7)
    parser.add_argument('--output', default=str(Path(__file__).with_name('halin-normalization-checks.json')))
    args = parser.parse_args()
    fixtures = []
    counts = Counter()
    maxima = {}
    first_lower = None
    first_deterministic_lower = None
    for d in range(3, args.max_ports+1):
        for shape_index, shape in enumerate(ordered_binary(1, d)):
            original, directed, rules, dual = fixture(shape, d)
            records = [selected_splits(x, rules, d) for x in range(1 << d)]
            support = set().union(*records)
            colors, rows = color_dual(d, dual)
            deterministic_rows = [tuple(pattern[c] for c in colors) for pattern in ((0,0,0), (0,1,1), (1,0,1), (1,1,0))]
            deterministic_union = set()
            for row in deterministic_rows:
                bits = sum(bit << i for i, bit in enumerate(row))
                deterministic_union |= records[bits]
                counts['deterministic_row_checks'] += 1
            assert deterministic_union == support
            if len(support) > 3*(d-3) and first_deterministic_lower is None:
                first_deterministic_lower = {'ports': d, 'shape_index': shape_index, 'shape': shape, 'splits': sorted(support), 'support_count': len(support), 'three_row_max': 3*(d-3)}
            for i, j in dual:
                for a, b in product((0, 1), repeat=2):
                    assert pair_covered(rows, i, j, a, b)
                    counts['signed_adjacent_pair_checks'] += 1
            if d <= 6:
                for x, splits in enumerate(records):
                    assert splits == independent_graph_splits(x, directed, d)
                    counts['independent_graph_switch_checks'] += 1
            patterns = list(product((0, 1), repeat=d)) if d <= 5 else [tuple([0]*d), tuple([1]*d), tuple(i%2 for i in range(d)), tuple((i+1)%2 for i in range(d))]
            worst = None
            for numerator, denominator in [(1, 8), (1, 4), (1, 2)]:
                for pattern in patterns:
                    probs = exact_probabilities(records, rows, [numerator if b == 0 else denominator-numerator for b in pattern], denominator)
                    for split in support:
                        p = max(env.get(split, Fraction(0)) for env in probs)
                        assert p >= Fraction(numerator, denominator)
                        ratio = p/Fraction(numerator, denominator)
                        worst = ratio if worst is None else min(worst, ratio)
                        counts['actual_target_probability_checks'] += 1
            active = active_ids(records, d)
            assert len(active) == (0 if d == 3 else d)
            row_search = two_rows_search(records, support, d) if d <= args.two_row_through else None
            bound = len(support) > 4*(d-3)
            if bound or (row_search is not None and not row_search['feasible']):
                if first_lower is None:
                    first_lower = {'ports': d, 'shape_index': shape_index, 'shape': shape,
                                   'splits': sorted(support), 'rows_search': row_search,
                                   'support_count_lower_bound': bound}
            maxima[d] = max(maxima.get(d, 0), len(support))
            counts['fixtures'] += 1
            counts['switching_trees'] += len(records)
            counts['local_active_detection'] += d
            fixtures.append({'ports': d, 'shape_index': shape_index, 'support_count': len(support),
                             'dual_edges': sorted(dual), 'colors': colors, 'rows': rows,
                             'deterministic_rows': deterministic_rows, 'active_ids': active, 'worst_tested_guarantee_ratio': str(worst),
                             'two_rows_at_fair_inheritance': row_search})
        print(json.dumps({'ports_completed': d, 'shapes': len(ordered_binary(1, d)), 'max_split_support': maxima[d], 'first_lower_bound_found': first_lower is not None}), flush=True)
    receipt = {'status': 'PASS', 'model': 'source-admitted rooted Halin bloblets; exact switching combinatorics',
               'parameters': vars(args), 'counts': dict(counts), 'max_split_support_by_ports': maxima,
               'first_actual_three_row_lower_bound_fixture': first_lower,
               'first_actual_four_row_deterministic_lower_bound_fixture': first_deterministic_lower,
               'limitations': ['Source embedding and LSA admission are explicit mathematical checks, not a general planarity algorithm.',
                               'Natural-probability corners exhaustive through five ports; four named corners thereafter.',
                               'Two-row impossibility search is only for fair inheritance and only through configured size.',
                               'No biological concordance-factor simulation or Lean verification.'],
               'fixtures': fixtures}
    Path(args.output).write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'status': 'PASS', 'counts': dict(counts), 'maxima': maxima, 'first_lower': first_lower, 'first_deterministic_lower': first_deterministic_lower}), flush=True)


if __name__ == '__main__':
    main()
