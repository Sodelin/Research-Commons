"""Exhaustive controls for the hidden-pair structural obstruction on five taxa.

Tests every nonempty family of all 15 binary trees as a candidate, every
nonempty family of the five trees compatible with the standard circle as a
baseline, and every hidden pair.  No network admission assumption is needed
for the obstruction.  The controls are not its all-size proof.
"""

from itertools import combinations
import json
from pathlib import Path
from adaptive_adversary_helpers import trees, splits, quartet_support, circular, canonical


def boundary_taxa(side, n):
    taxa = set()
    for x in range(n):
        y = (x + 1) % n
        if bool(side & (1 << x)) != bool(side & (1 << y)):
            taxa.update((x, y))
    assert len(taxa) == 4
    return taxa


def nontrivial_deletion(side, x, n):
    size = side.bit_count()
    member = bool(side & (1 << x))
    return size - member >= 2 and n - size - (not member) >= 2


def main():
    n = 5
    full = (1 << n) - 1
    circle = tuple(range(n))
    graphs = trees(n)
    assert len(graphs) == 15
    split_masks = sorted({s for graph in graphs for s in splits(graph, n)})
    split_index = {s: j for j, s in enumerate(split_masks)}
    circular_bits = sum(1 << j for j, s in enumerate(split_masks) if circular(s, circle))
    quartet_sets = list(combinations(range(n), 4))
    tree_support = [quartet_support(g, n, quartet_sets) for g in graphs]
    tree_split_bits = [sum(1 << split_index[s] for s in splits(g, n)) for g in graphs]
    planar = [j for j, ss in enumerate(tree_split_bits) if not ss & ~circular_bits]
    assert len(planar) == 5

    total = 1 << len(graphs)
    support = [0] * total
    split_union = [0] * total
    for family in range(1, total):
        bit = family & -family
        j = bit.bit_length() - 1
        prior = family ^ bit
        support[family] = support[prior] | tree_support[j]
        split_union[family] = split_union[prior] | tree_split_bits[j]

    pair_masks = {}
    for i, j in combinations(range(n), 2):
        excluded = sum(7 << (3 * p) for p, q in enumerate(quartet_sets)
                       if not {i, j}.issubset(q))
        pair_masks[(i, j)] = excluded

    higher_masks = {}
    for size in (3, 4):
        for hidden in combinations(range(n), size):
            higher_masks[hidden] = sum(7 << (3 * p) for p, q in enumerate(quartet_sets)
                                       if not set(hidden).issubset(q))
    consecutive_triples = {frozenset(circle[(p + shift) % n] for shift in range(3))
                           for p in range(n)}

    baselines = []
    for f in range(1, 1 << len(planar)):
        baselines.append(sum(1 << planar[p] for p in range(len(planar)) if (f >> p) & 1))
    report = {"status": "PASS", "n": n, "binary_trees": len(graphs),
              "candidate_families": total - 1, "baseline_families": len(baselines),
              "pair_transcript_checks": 0, "distinct_support_hidden_pair_matches": 0,
              "nonadjacent_matches": 0, "new_circular_splits_checked": 0,
              "new_noncircular_splits_checked": 0, "max_eligible_pairs_per_baseline": 0}
    report["higher_subset_transcript_checks"] = 0
    report["hidden_triple_matches"] = 0
    report["hidden_quartet_matches"] = 0
    report["max_eligible_triples_per_baseline"] = 0
    report["max_eligible_quartets_per_baseline"] = 0
    report["new_split_flip_origin_checks"] = 0
    report["hidden_subset_R_checks"] = 0
    report["noncircular_arc_checks"] = 0
    report["bounds_checked"] = {"pairs": "n+18k", "triples": "n+12k", "quartets": "3k"}

    for baseline in baselines:
        base_ss = split_union[baseline]
        neighbor_bits = 0
        for s in split_masks:
            if not (base_ss >> split_index[s]) & 1:
                continue
            for x in range(n):
                neighbor = canonical(s ^ (1 << x), n)
                if 2 <= neighbor.bit_count() <= n - 2 and circular(neighbor, circle):
                    neighbor_bits |= 1 << split_index[neighbor]
        assert neighbor_bits.bit_count() <= 4 * base_ss.bit_count()
        domains = {}
        records = 0
        for p, s in enumerate(split_masks):
            if not circular_bits & (1 << p) or base_ss & (1 << p):
                continue
            q = boundary_taxa(s, n)
            d = {x for x in q if nontrivial_deletion(s, x, n)}
            r = {x for x in d if base_ss & (1 << split_index[canonical(s ^ (1 << x), n)])}
            domains[p] = (q, d, r)
            records += len(r)
            possible_triples = [a for a in combinations(q, 3) if set(a) & d <= r]
            assert len(possible_triples) <= 2 * len(r)
            if d <= r:
                assert len(r) >= 2
        assert records <= 4 * base_ss.bit_count()
        eligible = set()
        higher_eligible = {3: set(), 4: set()}
        for candidate in range(1, total):
            if support[candidate] == support[baseline]:
                continue
            difference = support[candidate] ^ support[baseline]
            new_bits = split_union[candidate] & ~base_ss
            for pair, excluded in pair_masks.items():
                report["pair_transcript_checks"] += 1
                if difference & excluded:
                    continue
                eligible.add(pair)
                report["distinct_support_hidden_pair_matches"] += 1
                i, j = pair
                cherry_bit = 1 << split_index[canonical((1 << i) | (1 << j), n)]
                adjacent = ((j - i) % n in (1, n - 1))
                report["nonadjacent_matches"] += int(not adjacent)
                for p, s in enumerate(split_masks):
                    bit = 1 << p
                    if not new_bits & bit:
                        continue
                    if circular_bits & bit:
                        assert bit == cherry_bit or neighbor_bits & bit
                        report["new_circular_splits_checked"] += 1
                        if not adjacent:
                            origins = {x for x in pair if nontrivial_deletion(s, x, n)
                                       and base_ss & (1 << split_index[canonical(s ^ (1 << x), n)])}
                            assert origins
                            assert origins <= boundary_taxa(s, n)
                            report["new_split_flip_origin_checks"] += 1
                    else:
                        if not adjacent:
                            assert bit == cherry_bit
                            arcs = (range(i + 1, j), list(range(j + 1, n)) + list(range(0, i)))
                            for arc in arcs:
                                arc = list(arc)
                                if len(arc) < 2:
                                    continue
                                arc_side = canonical(sum(1 << x for x in arc), n)
                                arc_bit = 1 << split_index[arc_side]
                                assert split_union[candidate] & arc_bit
                                if not base_ss & arc_bit:
                                    for x in pair:
                                        assert nontrivial_deletion(arc_side, x, n)
                                        lifted = canonical(arc_side ^ (1 << x), n)
                                        assert base_ss & (1 << split_index[lifted])
                                report["noncircular_arc_checks"] += 1
                        report["new_noncircular_splits_checked"] += 1
            for hidden, excluded in higher_masks.items():
                report["higher_subset_transcript_checks"] += 1
                if difference & excluded:
                    continue
                size = len(hidden)
                higher_eligible[size].add(hidden)
                report["hidden_triple_matches" if size == 3 else "hidden_quartet_matches"] += 1
                assert not (new_bits & circular_bits & ~neighbor_bits)
                for p, (q, d, r) in domains.items():
                    if new_bits & (1 << p):
                        assert set(hidden) & d <= r
                        report["hidden_subset_R_checks"] += 1
                if split_union[candidate] & ~circular_bits:
                    assert size == 3
                    assert frozenset(hidden) in consecutive_triples
        assert len(eligible) <= n + 18 * base_ss.bit_count()
        report["max_eligible_pairs_per_baseline"] = max(
            report["max_eligible_pairs_per_baseline"], len(eligible))
        assert len(higher_eligible[3]) <= n + 12 * base_ss.bit_count()
        assert len(higher_eligible[4]) <= 3 * base_ss.bit_count()
        report["max_eligible_triples_per_baseline"] = max(
            report["max_eligible_triples_per_baseline"], len(higher_eligible[3]))
        report["max_eligible_quartets_per_baseline"] = max(
            report["max_eligible_quartets_per_baseline"], len(higher_eligible[4]))
    path = Path(__file__).with_name("adaptive-adversary-pair-controls.json")
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
