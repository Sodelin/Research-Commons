"""Exact control-menu -> quartet provider -> PINNED sparse decoder checks.

This executes analytical NMSCcom mixtures, not coalescent simulations or
physical interventions. Compatible orders use finite exhaustive permutations,
not a production order learner. Original provider code is an immutable external
scratch dependency; its canonical Git blob and SHA256 are asserted before use.

Run from this directory with the original sparse_quartet.py materialized at
/tmp/control-menu-provider/sparse_quartet.py (or --provider PATH).
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
from fractions import Fraction
from hashlib import sha1, sha256
import importlib.util
from itertools import combinations, permutations, product
import json
from pathlib import Path
import sys

import menu_checks as menu

PROVIDER_COMMIT = 'a1ae2891fd4bcd1dafe27321c97d655eac7b5e97'
PROVIDER_PATH = 'research/2026-09-30-astra-sparse-query/sparse_quartet.py'
PROVIDER_BLOB = '49933337ce26ce0d5ef58bbfa458bf5706d8e817'
PROVIDER_SHA256 = '2dd411db0ceb248cb42549eca06c0f1e8510f7ba1837fe544e9ef83e7cefc1fa'


def import_provider(path):
    raw = path.read_bytes()
    actual_sha256 = sha256(raw).hexdigest()
    actual_blob = sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    assert actual_blob == PROVIDER_BLOB, (actual_blob, PROVIDER_BLOB)
    assert actual_sha256 == PROVIDER_SHA256, (actual_sha256, PROVIDER_SHA256)
    spec = importlib.util.spec_from_file_location('original_sparse_quartet', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module, {'canonical_git_blob': actual_blob, 'sha256': actual_sha256,
                    'bytes': len(raw), 'commons_commit': PROVIDER_COMMIT,
                    'repository_path': PROVIDER_PATH}


def canonical_side(side, labels):
    complement = set(labels) - set(side)
    return min(tuple(sorted(side)), tuple(sorted(complement)))


def fixture(r, active, required, n):
    """Binary D-side grafts preserve the admitted raw gadget's source class.

    n=5: replace R->D by R->d0, d0->D,E.
    n=6: replace R->D by R->d0, d0->D,d1, d1->E,F.
    All grafts are tree edges outside every hybrid blob, every new leaf is on
    the exterior, and R remains LSA of all taxa. Degree/DAG checks run below;
    exterior-planarity and galled admission are these direct manual arguments.
    """
    edges, hybrids = menu.gadget(r, active, required)
    labels = tuple('ABCDEF'[:n])
    if n > 4:
        edges.remove(('R', 'D'))
        edges += [('R', 'd0'), ('d0', 'D')]
        if n == 5:
            edges += [('d0', 'E')]
        else:
            edges += [('d0', 'd1'), ('d1', 'E'), ('d1', 'F')]
    raw = edges + [(parent, h) for h, opts in hybrids.values()
                   for parent in opts.values()]
    vertices = {v for e in raw for v in e}
    for v in vertices:
        degree = (sum(b == v for a, b in raw), sum(a == v for a, b in raw))
        expected = {(0, 2)} if v == 'R' else {(1, 0)} if v in labels else {(1, 2), (2, 1)}
        assert degree in expected, (v, degree)
    removed = set()
    while removed != vertices:
        ready = {v for v in vertices - removed
                 if all(a in removed for a, b in raw if b == v)}
        assert ready, 'Directed cycle in fixture'
        removed |= ready
    return edges, hybrids, labels


def tree_observations(edges, labels):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    assert len(edges) == len(adj) - 1
    distance = {}
    for label in labels:
        dist = {label: 0}
        todo = [label]
        while todo:
            v = todo.pop()
            for w in adj[v]:
                if w not in dist:
                    dist[w] = dist[v] + 1
                    todo.append(w)
        assert len(dist) == len(adj)
        distance[label] = dist
    quartets = {}
    for q in combinations(labels, 4):
        a, b, c, d = q
        sums = (distance[a][b] + distance[c][d],
                distance[a][c] + distance[b][d],
                distance[a][d] + distance[b][c])
        low = min(sums)
        assert sums.count(low) == 1, (q, sums)
        others = [s for s in sums if s != low]
        assert others[0] == others[1]
        assert (others[0] - low) % 2 == 0
        ell_units = (others[0] - low) // 2
        assert ell_units >= 1
        quartets[q] = (sums.index(low), ell_units)
    # Truth is obtained from every actual switched-tree edge, not from Q.
    splits = set()
    for a, b in edges:
        seen = {a}
        todo = [a]
        while todo:
            v = todo.pop()
            for w in adj[v]:
                if {v, w} == {a, b} or w in seen:
                    continue
                seen.add(w)
                todo.append(w)
        side = set(labels) & seen
        if 2 <= len(side) <= len(labels) - 2:
            splits.add(canonical_side(side, labels))
    return quartets, splits


def analytic_provider(records, rows, ps, labels):
    truth_q = {q: set() for q in combinations(labels, 4)}
    truth_splits = set()
    for bits, qs, splits in records:
        truth_splits |= splits
        for q, (t, ell) in qs.items():
            truth_q[q].add(t)
    assert all(1 <= len(v) <= 2 for v in truth_q.values())
    maxima = {q: [Fraction(0)] * 3 for q in truth_q}
    rows_receipt = []
    for row in rows:
        cf = {q: [Fraction(0)] * 3 for q in truth_q}
        total_weight = Fraction(0)
        for bits, qs, splits in records:
            if any(c is not None and bits[i] != c for i, c in enumerate(row)):
                continue
            weight = Fraction(1)
            for i, c in enumerate(row):
                if c is None:
                    weight *= ps[i] if bits[i] else 1 - ps[i]
            total_weight += weight
            for q, (t, ell) in qs.items():
                # Every original edge has coalescent length ln(2); suppression
                # adds lengths. Tree MSC discordant probability is exp(-ell)/3.
                x = Fraction(1, 2) ** ell
                for u in range(3):
                    cf[q][u] += weight * (x / 3 + (1 - x if u == t else 0))
        assert total_weight == 1
        for q, probs in cf.items():
            assert sum(probs) == 1
            baseline = min(probs)
            for t in range(3):
                maxima[q][t] = max(maxima[q][t], probs[t] - baseline)
        rows_receipt.append({'controls': [c for c in row],
                             'cf': {' '.join(q): [str(v) for v in probs]
                                    for q, probs in cf.items()}})
    g = min(min(p, 1 - p) for p in ps)
    delta = g / 2
    recovered = {q: {t for t in range(3) if contrasts[t] > delta / 2}
                 for q, contrasts in maxima.items()}
    assert recovered == truth_q
    positive = [maxima[q][t] for q, support in truth_q.items() for t in support]
    assert min(positive) >= delta
    assert all(maxima[q][t] == 0 for q, support in truth_q.items()
               for t in range(3) if t not in support)
    return recovered, truth_splits, minima(positive), rows_receipt, maxima


def minima(values):
    return str(min(values))


def topology_partition(q, t):
    # In global sorted coordinates t=0,1,2 pair the first taxon with 1,2,3.
    side = {q[0], q[t + 1]}
    return canonical_side(side, q)


def remapped_mask(index_quartet, order, support):
    chosen_labels = tuple(order[i] for i in index_quartet)
    global_q = tuple(sorted(chosen_labels))
    partitions = {topology_partition(global_q, t) for t in support[global_q]}
    return sum(1 << t for t in range(3)
               if topology_partition(chosen_labels, t) in partitions)


def learn_order_by_finite_enumeration(labels, support):
    checked = 0
    # Intentionally enumerate changed label orders first. This exercises the
    # topology-mask adapter; an identity-order shortcut would hide label bugs.
    for tail in permutations(tuple(reversed(labels[1:]))):
        order = (labels[0],) + tail
        checked += 1
        if all(not remapped_mask(q, order, support) & 2
               for q in combinations(range(len(labels)), 4)):
            return order, checked
    raise AssertionError('No compatible circular order exists')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--provider', type=Path,
                        default=Path('/tmp/control-menu-provider/sparse_quartet.py'))
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('integration-checks.json'))
    args = parser.parse_args()
    decoder, provenance = import_provider(args.provider)
    counts = {'admitted_gadget_fixtures': 0, 'switched_trees': 0,
              'tree_quartet_internal_lengths': 0, 'analytical_environment_readouts': 0,
              'analytical_quartet_cf_vectors': 0, 'support_quartets_checked': 0,
              'sparse_decoder_runs': 0, 'decoder_oracle_calls': 0,
              'compatible_orders_checked': 0, 'changed_label_order_runs': 0,
              'nonidentity_mask_remaps_checked': 0}
    fixtures = []
    detailed = None
    g = Fraction(1, 8)
    for n in range(4, 7):
        for r in range(2, 7):
            rows = menu.partial_array(r)
            assert menu.covers(rows, r)
            for active in combinations(range(r), 2):
                for required in product((0, 1), repeat=2):
                    base, hybrids, labels = fixture(r, active, required, n)
                    records = []
                    for bits in product((0, 1), repeat=r):
                        selected = base + [(hybrids[i][1][bits[i]], hybrids[i][0])
                                           for i in range(r)]
                        qs, splits = tree_observations(selected, labels)
                        records.append((bits, qs, splits))
                    ps = [Fraction(1, 2)] * r
                    for i, a in zip(active, required):
                        ps[i] = g if a else 1 - g
                    supported_q, truth_splits, min_contrast, readouts, maxima = analytic_provider(
                        records, rows, ps, labels)
                    order, order_checks = learn_order_by_finite_enumeration(labels, supported_q)
                    oracle = lambda q: remapped_mask(q, order, supported_q)
                    result = decoder.recover(n, oracle)
                    actual_splits = {canonical_side({order[t] for t in range(i + 1, j + 1)}, labels)
                                     for i, j in result.splits}
                    assert actual_splits == truth_splits, (n, r, active, required,
                                                          actual_splits, truth_splits)
                    assert result.oracle_calls <= decoder.query_bound(n, len(truth_splits))
                    # Finite independent check of adapter partition mapping.
                    for q in combinations(range(n), 4):
                        global_q = tuple(sorted(order[i] for i in q))
                        global_mask = sum(1 << t for t in supported_q[global_q])
                        mapped = oracle(q)
                        original_partitions = {topology_partition(global_q, t)
                                               for t in supported_q[global_q]}
                        mapped_partitions = {topology_partition(tuple(order[i] for i in q), t)
                                             for t in range(3) if mapped & (1 << t)}
                        assert original_partitions == mapped_partitions
                        counts['nonidentity_mask_remaps_checked'] += int(mapped != global_mask)
                    counts['admitted_gadget_fixtures'] += 1
                    counts['switched_trees'] += len(records)
                    counts['tree_quartet_internal_lengths'] += len(records) * len(supported_q)
                    counts['analytical_environment_readouts'] += len(rows)
                    counts['analytical_quartet_cf_vectors'] += len(rows) * len(supported_q)
                    counts['support_quartets_checked'] += len(supported_q)
                    counts['sparse_decoder_runs'] += 1
                    counts['decoder_oracle_calls'] += result.oracle_calls
                    counts['compatible_orders_checked'] += order_checks
                    counts['changed_label_order_runs'] += int(order != labels)
                    entry = {'n': n, 'r': r, 'active_hybrids': active,
                             'rare_required_choices': required, 'menu_environments': len(rows),
                             'compatible_order': order, 'order_candidates_checked': order_checks,
                             'quartet_count': len(supported_q),
                             'truth_split_count': len(truth_splits),
                             'minimum_positive_max_contrast': min_contrast,
                             'decoder': asdict(result), 'exact_Q_matches': True,
                             'complete_displayed_split_union_matches': True}
                    entry['decoder']['splits'] = sorted(result.splits)
                    fixtures.append(entry)
                    if n == 6 and r == 6 and active == (0, 1) and required == (1, 1):
                        detailed = {'fixture': entry,
                                    'tree_edge_truth_split_union': sorted(truth_splits),
                                    'recovered_Q': {' '.join(q): sorted(ts)
                                                    for q, ts in supported_q.items()},
                                    'maximum_contrasts': {' '.join(q): [str(x) for x in v]
                                                          for q, v in maxima.items()},
                                    'exact_environment_CF_readouts': readouts}
    assert counts['admitted_gadget_fixtures'] == 420
    assert counts['nonidentity_mask_remaps_checked'] > 0
    assert detailed is not None
    receipt = {'kind': 'Executed exact analytical fixture pipeline with original pinned decoder',
               'source_admission': 'Manual exterior/galled/LSA proof; executed binary-degree/DAG/tree checks',
               'observation_mechanism': 'Ideal controlled NMSCcom; not NMSCind',
               'inheritance_floor_g': str(g), 'edge_length': 'ln(2) coalescent units',
               'quartet_length_floor_tau': 'ln(2)', 'Delta': str(g / 2),
               'classification_threshold_Delta_over_2': str(g / 4),
               'provider_provenance': provenance, 'counts': counts,
               'fixtures': fixtures, 'representative_detailed_fixture': detailed,
               'not_executed': ['IID locus sampling', 'biological interventions',
                                'NMSCind partial-control observations',
                                'production constructive order learner',
                                'source/intervention-preserving normalization',
                                'formal proof or Lean', 'general-network enumeration'],
               'claim_boundary': 'Finite nontrivial source-admitted fixtures corroborate the conditional integration; no all-class computational proof or master closure.'}
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'provider_provenance': provenance, 'counts': counts,
                      'output': str(args.output)}, indent=2))


if __name__ == '__main__':
    main()
