"""Exact passive-vs-controlled normalization discriminator under NMSCcom.

A source-admitted serial bigon lies above a B,E cherry. Its two parental
arcs have different positive coalescent lengths. Passive collapse preserves
all quartet concordance factors and support. Retained active controls commute
with collapse. Forcing the removed bigon changes CFs, disproving preservation
by one FIXED effective edge for every original intervention.

This is exact analytical tree-MSC mixture arithmetic, not an NMSCind result,
physical intervention, full-joint-law result, or formal source-class proof.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt
import json
from pathlib import Path

import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "2026-09-30-control-menu-continuation"))
import menu_checks as menu
from integration_checks import tree_observations

LABELS = tuple('ABCDE')
G = F(1, 8)


def source_fixture():
    edges, hybrids = menu.gadget(3)
    edges.remove(('H2', 'B'))
    edges += [('H2', 's'), ('s', 'B'), ('s', 'E')]
    normalized = [e for e in edges if e not in [('v0', 'u2'), ('H2', 's')]]
    normalized += [('v0', 's')]
    retained = {i: hybrids[i] for i in (0, 1)}
    for base, hs in [(edges, hybrids), (normalized, retained)]:
        raw = base + [(parent, h) for h, opts in hs.values() for parent in opts.values()]
        vertices = {v for e in raw for v in e}
        for v in vertices:
            degrees = (sum(b == v for a, b in raw), sum(a == v for a, b in raw))
            expected = {(0, 2)} if v == 'R' else {(1, 0)} if v in LABELS else {(1, 2), (2, 1)}
            assert degrees in expected
        seen = set()
        while seen != vertices:
            ready = {v for v in vertices - seen if all(a in seen for a, b in raw if b == v)}
            assert ready
            seen |= ready
    # Manual source admission: original outer-planar level-two blob is retained;
    # padding bigon is a separate exterior blob with cut child edge; the new
    # B,E cherry and normalized v0->s edge are tree grafts. All taxa are exterior,
    # every hybrid child edge is a cut edge, R is LSA. Parallel arcs are admitted.
    return edges, hybrids, normalized, retained


def weighted_quartets(edges):
    unweighted = [(a, b) for a, b, survival in edges]
    topologies, splits = tree_observations(unweighted, LABELS)
    adj = {}
    for a, b, survival in edges:
        assert 0 < survival < 1, 'Every original/effective length is strictly positive'
        adj.setdefault(a, []).append((b, survival))
        adj.setdefault(b, []).append((a, survival))
    path_survival = {}
    for source in LABELS:
        dist = {source: F(1)}
        todo = [source]
        while todo:
            v = todo.pop()
            for w, survival in adj[v]:
                if w not in dist:
                    dist[w] = dist[v] * survival
                    todo.append(w)
        path_survival[source] = dist
    result = {}
    for q, (t, units) in topologies.items():
        a, b, c, d = q
        values = [path_survival[a][b] * path_survival[c][d],
                  path_survival[a][c] * path_survival[b][d],
                  path_survival[a][d] * path_survival[b][c]]
        assert values[t] == max(values) and values.count(values[t]) == 1
        others = [x for i, x in enumerate(values) if i != t]
        assert others[0] == others[1]
        ratio = others[0] / values[t]
        numerator, denominator = isqrt(ratio.numerator), isqrt(ratio.denominator)
        assert numerator ** 2 == ratio.numerator and denominator ** 2 == ratio.denominator
        survival = F(numerator, denominator)
        assert 0 < survival <= F(1, 2), 'Quartet length floor ln(2) is maintained'
        result[q] = (t, survival)
    return result, splits


def records(base, hybrids, effective_survival=None):
    result = []
    for bits in product((0, 1), repeat=len(hybrids)):
        edges = [(a, b, effective_survival if (a, b) == ('v0', 's') else F(1, 2))
                 for a, b in base]
        for i, (h, parents) in hybrids.items():
            arc_survival = (F(1, 2) if bits[i] == 0 else F(1, 4)) if i == 2 else F(1, 2)
            edges.append((parents[bits[i]], h, arc_survival))
        qs, splits = weighted_quartets(edges)
        result.append((bits, qs, splits))
    return result


def cf(recs, row, probs):
    vectors = {q: [F(0)] * 3 for q in combinations(LABELS, 4)}
    masses = {q: [F(0)] * 3 for q in combinations(LABELS, 4)}
    total = F(0)
    for bits, qs, splits in recs:
        if any(c is not None and bits[i] != c for i, c in enumerate(row)):
            continue
        weight = F(1)
        for i, c in enumerate(row):
            if c is None:
                weight *= probs[i] if bits[i] else 1 - probs[i]
        total += weight
        for q, (t, survival) in qs.items():
            masses[q][t] += weight
            for u in range(3):
                vectors[q][u] += weight * (survival / 3 + (1 - survival if u == t else 0))
    assert total == 1
    assert all(sum(v) == 1 for v in vectors.values())
    return vectors, masses


def json_vectors(vectors):
    return {' '.join(q): [str(x) for x in v] for q, v in vectors.items()}


def support_and_splits(recs):
    support = {q: set() for q in combinations(LABELS, 4)}
    all_splits = set()
    for bits, qs, splits in recs:
        for q, (t, survival) in qs.items():
            support[q].add(t)
        all_splits |= splits
    return support, all_splits


def main():
    base, hs, normalized, retained = source_fixture()
    natural_probs = [G, G, F(1, 2)]
    # Surrounding v0->u2 and H2->s edges both have survival 1/2.
    passive_survival = F(1, 2) * (F(1, 2) * F(1, 2) + F(1, 2) * F(1, 4)) * F(1, 2)
    assert passive_survival == F(3, 32)
    original_records = records(base, hs)
    normalized_records = records(normalized, retained, passive_survival)
    passive_original, _ = cf(original_records, (None, None, None), natural_probs)
    passive_normalized, _ = cf(normalized_records, (None, None), natural_probs[:2])
    assert passive_original == passive_normalized
    source_support, source_splits = support_and_splits(original_records)
    normalized_support, normalized_splits = support_and_splits(normalized_records)
    assert source_support == normalized_support and source_splits == normalized_splits
    assert all(len(s) <= 2 for s in source_support.values())

    # Full intervention-lift on retained active controls: all nine partial rows.
    retained_readouts = []
    for row in product((0, None, 1), repeat=2):
        original, _ = cf(original_records, row + (None,), natural_probs)
        reduced, _ = cf(normalized_records, row, natural_probs[:2])
        assert original == reduced
        retained_readouts.append({'effective_row': row, 'original_lift': row + (None,),
                                  'all_five_quartet_CFs_equal': True})

    forced = []
    for choice in (0, 1):
        row = (None, None, choice)
        vectors, _ = cf(original_records, row, natural_probs)
        effective = F(1, 8) if choice == 0 else F(1, 16)
        adjusted_records = records(normalized, retained, effective)
        adjusted_vectors, _ = cf(adjusted_records, (None, None), natural_probs[:2])
        assert vectors == adjusted_vectors
        assert vectors != passive_normalized
        differing = {q: v for q, v in vectors.items() if v != passive_normalized[q]}
        assert len(differing) == 3  # Quartets containing both B and E.
        forced.append({'removed_bigon_choice': choice,
                       'required_effective_survival': str(effective),
                       'all_quartet_CF_readouts': json_vectors(vectors),
                       'quartets_changed_from_fixed_passive_collapse': [' '.join(q) for q in differing],
                       'environment_dependent_effective_edge_recovers_CFs': True})
    assert forced[0]['all_quartet_CF_readouts'] != forced[1]['all_quartet_CF_readouts']
    assert support_and_splits(original_records)[0] == source_support

    # A compact discriminating table with both active parents fixed: ABDE has
    # sole species topology AD|BE; only the neutral bigon's length is varied.
    q = tuple('ABDE')
    simple_readouts = []
    for choice in (None, 0, 1):
        vectors, _ = cf(original_records, (1, 1, choice), natural_probs)
        simple_readouts.append({'bigon_setting': choice,
                                'quartet_ABDE_CF_order_AB_DE_AD_BE_AE_BD': list(map(str, vectors[q]))})
    assert simple_readouts[0]['quartet_ABDE_CF_order_AB_DE_AD_BE_AE_BD'] == ['1/64', '31/32', '1/64']
    assert simple_readouts[1]['quartet_ABDE_CF_order_AB_DE_AD_BE_AE_BD'] == ['1/48', '23/24', '1/48']
    assert simple_readouts[2]['quartet_ABDE_CF_order_AB_DE_AD_BE_AE_BD'] == ['1/96', '47/48', '1/96']

    # A graph-informed support-control projection removes the neutral ID2 and
    # reduces the exact effective menu from m_g(3)=3 to m_g(2)=2 environments.
    rows = menu.partial_array(2)
    maxima = {q: [F(0)] * 3 for q in source_support}
    massmax = {q: [F(0)] * 3 for q in source_support}
    for row in rows:
        vectors, masses = cf(original_records, tuple(row) + (None,), natural_probs)
        for q, vector in vectors.items():
            for t in range(3):
                maxima[q][t] = max(maxima[q][t], vector[t] - min(vector))
                massmax[q][t] = max(massmax[q][t], masses[q][t])
    delta = G / 2
    recovered = {q: {t for t in range(3) if maxima[q][t] > delta / 2} for q in source_support}
    assert recovered == source_support
    supported_masses = [massmax[q][t] for q, ts in source_support.items() for t in ts]
    supported_contrasts = [maxima[q][t] for q, ts in source_support.items() for t in ts]
    assert min(supported_masses) >= G and min(supported_contrasts) >= delta
    assert all(maxima[q][t] == 0 for q, ts in source_support.items() for t in range(3) if t not in ts)
    receipt = {'kind': 'Executed exact passive-versus-controlled normalization discriminator',
               'source_class_admission': 'Manual outer-planar/galled/LSA preservation; binary-degree/DAG/tree checks executed',
               'source_model': 'Ideal NMSCcom, product switching weights followed by tree MSC',
               'taxa': LABELS, 'original_r': 3, 'retained_effective_r': 2,
               'original_switching_trees': len(original_records),
               'normalized_switching_trees': len(normalized_records),
               'quartet_count': len(source_support),
               'inheritance_probabilities_for_choice_1': list(map(str, natural_probs)),
               'original_bigon_arc_survivals': ['1/2', '1/4'],
               'original_bigon_arc_lengths': ['ln(2)', 'ln(4)'],
               'passive_collapsed_chain_survival': str(passive_survival),
               'passive_collapsed_chain_length': 'ln(32/3)',
               'passive_all_quartet_CFs_preserved': True,
               'passive_original_CF_readouts': json_vectors(passive_original),
               'displayed_quartet_support_preserved': True,
               'complete_displayed_split_union_preserved': True,
               'tree_edge_split_union': sorted(source_splits),
               'all_nine_retained_partial_control_rows_preserve_CFs': retained_readouts,
               'removed_bigon_forced_readouts': forced,
               'simple_discriminator_with_active_HA_HC_fixed_to_1': simple_readouts,
               'one_fixed_passive_edge_preserves_both_removed_controls': False,
               'support_control_projection': {
                   'effective_controls': ['HA', 'HC'], 'removed_support_neutral_control': 'H2',
                   'lift': 'Retain coordinates0,1 and leave coordinate2 random',
                   'original_menu_environments': menu.partial_count(3),
                   'effective_menu_environments': menu.partial_count(2),
                   'effective_rows': rows,
                   'exact_quartet_support_recovered': True,
                   'minimum_supported_switching_mass_over_best_environment': str(min(supported_masses)),
                   'minimum_supported_CF_contrast_over_best_environment': str(min(supported_contrasts)),
                   'original_tau_floor': 'ln(2)', 'Delta': str(delta),
                   'classification_threshold': str(delta / 2)},
               'not_executed': ['NMSCind', 'full joint gene-tree law comparison',
                                'biological interventions', 'general normalization algorithm',
                                'source-admission formalization', 'Lean', 'IID locus sampling'],
               'claim_boundary': 'One admitted counterexample distinguishes passive CF preservation from all-original-control law preservation. The projection is graph-informed and proved/checkable for this fixture, not a universal control quotient.'}
    path = Path(__file__).with_name('normalization-effects-checks.json')
    path.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ['original_r', 'retained_effective_r',
        'passive_all_quartet_CFs_preserved', 'complete_displayed_split_union_preserved',
        'one_fixed_passive_edge_preserves_both_removed_controls', 'support_control_projection']}, indent=2))


if __name__ == '__main__':
    main()
