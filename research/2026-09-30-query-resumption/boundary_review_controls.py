"""Independent finite controls for the boundary review, not all-size proofs."""

from itertools import combinations
import json
from pathlib import Path

from adaptive_adversary_helpers import quartet_support


def caterpillar(n):
    graph = {v: set() for v in range(2 * n - 2)}

    def edge(a, b):
        graph[a].add(b)
        graph[b].add(a)

    leaf_arms = []
    for t in range(n - 2):
        leaves = [0, 1] if t == 0 else [n - 2, n - 1] if t == n - 3 else [t + 1]
        leaf_arms.append(leaves)
        for x in leaves:
            edge(n + t, x)
        if t:
            edge(n + t - 1, n + t)
    return graph, leaf_arms


def swap_leaves(graph, i, j):
    mapping = {i: j, j: i}
    return {mapping.get(v, v): {mapping.get(w, w) for w in neighbors}
            for v, neighbors in graph.items()}


def run():
    linear_witness = []
    total_candidate_checks = 0
    for n in range(5, 13):
        graph, arms = caterpillar(n)
        quartets = list(combinations(range(n), 4))
        baseline = quartet_support(graph, n, quartets)
        hidden_pairs = {tuple(sorted((i, j)))
                        for left, right in zip(arms, arms[1:])
                        for i in left for j in right}
        assert len(hidden_pairs) == n - 1
        for i, j in hidden_pairs:
            candidate = quartet_support(swap_leaves(graph, i, j), n, quartets)
            difference = baseline ^ candidate
            assert difference
            for p, q in enumerate(quartets):
                if not {i, j}.issubset(q):
                    assert not difference & (7 << (3 * p))
            total_candidate_checks += 1
        linear_witness.append({"n": n, "eligible_pairs_demonstrated": len(hidden_pairs)})

    distance_inversions = 0
    quartet_regenerations = 0
    for n in range(4, 7):
        full = (1 << n) - 1
        dictionary = []
        for i, j in combinations(range(n), 2):
            if j == i + 1 or (i == 0 and j == n - 1):
                continue
            side = sum(1 << x for x in range(i + 1, j + 1))
            dictionary.append((i, j, min(side, full ^ side)))
        for mask in range(1 << len(dictionary)):
            original = {s for p, (_, _, s) in enumerate(dictionary) if mask & (1 << p)}
            d = [[0 if x == y else 2 + sum(bool(s & (1 << x)) != bool(s & (1 << y))
                                          for s in original)
                  for y in range(n)] for x in range(n)]
            recovered = set()
            for i, j, s in dictionary:
                a, b, c, e = i, (i + 1) % n, j, (j + 1) % n
                twice = d[a][c] + d[b][e] - d[a][e] - d[b][c]
                assert twice in (0, 2)
                if twice:
                    recovered.add(s)
            assert recovered == original
            distance_inversions += 1
            for q in combinations(range(n), 4):
                selected = sum(1 << x for x in q)
                topology = lambda ss: {min(s & selected, selected ^ (s & selected))
                                       for s in ss if (s & selected).bit_count() == 2}
                assert topology(recovered) == topology(original)
                quartet_regenerations += 1

    # A bad modulus can alias distinct candidate IDs even at cardinality one.
    # With p=2 and M=3, support {1} and support {3} have identical power sums.
    p = 2
    bad_modulus_collision = all(pow(1, j, p) == pow(3, j, p) for j in range(8))
    assert bad_modulus_collision

    return {"status": "PASS", "caterpillar_hidden_pair_candidates_checked": total_candidate_checks,
            "linear_witness": linear_witness,
            "exhaustive_circular_split_distance_inversions_n4_to_n6": distance_inversions,
            "exhaustive_regenerated_quartet_supports": quartet_regenerations,
            "bad_modulus_collision_p2_M3": bad_modulus_collision,
            "scope": "Finite controls only. Arbitrary circular subsets test algebra, not source admission. The caterpillar witnesses are admitted binary trees."}


if __name__ == "__main__":
    result = run()
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
