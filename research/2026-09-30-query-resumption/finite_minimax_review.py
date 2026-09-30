"""Independent graph replay and all-path certificate for exact five-taxon optimum.

Uses inherited graph fixture admission, but derives displayed support again
from actual switching trees using path distances, independently of saved split
unions and the reviewed minimax implementation. Standard library only.
"""

from collections import deque
from functools import lru_cache
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib
import json
from adaptive_adversary_helpers import trees, circular


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "2026-09-30-root-exact-query/anchor-collision-receipt.json"
N = 5
FULL = (1 << N) - 1
QUARTETS = list(combinations(range(N), 4))


def graph_splits(graph, labels):
    found = set()
    visited_edges = set()
    for u in graph:
        for v in graph[u]:
            excluded = frozenset((u, v))
            if excluded in visited_edges:
                continue
            visited_edges.add(excluded)
            seen = set()
            queue = [u]
            while queue:
                a = queue.pop()
                if a in seen:
                    continue
                seen.add(a)
                queue.extend(b for b in graph[a] - seen if frozenset((a, b)) != excluded)
            side = sum(1 << labels[a] for a in seen if a in labels)
            side = min(side, FULL ^ side)
            if 2 <= side.bit_count() <= N - 2:
                found.add(side)
    return frozenset(found)


def distance_profile(graph, labels):
    inverse = {taxon: vertex for vertex, taxon in labels.items()}
    distances = {}
    for x in range(N):
        start = inverse[x]
        dist = {start: 0}
        queue = deque([start])
        while queue:
            a = queue.popleft()
            for b in graph[a]:
                if b not in dist:
                    dist[b] = dist[a] + 1
                    queue.append(b)
        assert set(dist) == set(graph)
        distances[x] = {y: dist[inverse[y]] for y in range(N)}
    assert sum(map(len, graph.values())) // 2 == len(graph) - 1
    profile = []
    for a, b, c, d in QUARTETS:
        scores = (distances[a][b] + distances[c][d],
                  distances[a][c] + distances[b][d],
                  distances[a][d] + distances[b][c])
        assert scores.count(min(scores)) == 1
        profile.append(1 << scores.index(min(scores)))
    return tuple(profile)


def fixture_display(fixture, relabel):
    hybrids = list(fixture["hybrids"])
    union = set()
    profile = [0] * len(QUARTETS)
    distinct = set()
    for choices in product((0, 1), repeat=len(hybrids)):
        graph = {}
        for u, v in fixture["edges"]:
            graph.setdefault(u, set()).add(v)
            graph.setdefault(v, set()).add(u)
        for hybrid, choice in zip(hybrids, choices):
            deleted_parent = fixture["hybrids"][hybrid][1 - choice]
            graph[hybrid].remove(deleted_parent)
            graph[deleted_parent].remove(hybrid)
        labels = {f"T{x}": relabel[x] for x in range(N)}
        tree_profile = distance_profile(graph, labels)
        ss = graph_splits(graph, labels)
        distinct.add(ss)
        union.update(ss)
        for q, value in enumerate(tree_profile):
            profile[q] |= value
    return tuple(profile), frozenset(union), len(distinct)


def minimax(profiles, targets):
    @lru_cache(None)
    def solve(state):
        if len({targets[i] for i in state}) <= 1:
            return 0
        costs = []
        for q in range(len(QUARTETS)):
            outcomes = {}
            for i in state:
                outcomes.setdefault(profiles[i][q], []).append(i)
            if len(outcomes) < 2:
                continue
            costs.append(1 + max(solve(tuple(group)) for group in outcomes.values()))
        assert costs
        return min(costs)
    value = solve(tuple(range(len(profiles))))
    return {"optimal_worst_case_queries": value,
            "memoized_states": solve.cache_info().currsize}


def main():
    saved = json.loads(SOURCE.read_text())
    assert saved["status"] == "PASS"
    fixtures = {f["name"]: f for f in saved["fixtures"]}
    circle = tuple(range(N))
    base_p, base_s, base_tree_count = fixture_display(fixtures["N2"], circle)
    assert base_p == (5,) * 5
    assert base_tree_count == 4
    cycle_splits = {min((1 << x) | (1 << ((x + 1) % N)),
                        FULL ^ ((1 << x) | (1 << ((x + 1) % N)))) for x in range(N)}
    assert base_s == cycle_splits

    local_candidates = []
    for shift in range(N):
        relabel = tuple((x + shift) % N for x in range(N))
        p, ss, count = fixture_display(fixtures["N1"], relabel)
        exceptional = tuple(x for x in range(N) if x != shift)
        qi = QUARTETS.index(exceptional)
        assert [j for j in range(5) if p[j] != base_p[j]] == [qi]
        assert count == 3 and ss < base_s and len(base_s - ss) == 1
        assert all(circular(s, circle) for s in ss)
        local_candidates.append({"shift": shift, "relabel": relabel,
                                 "exceptional_quartet": exceptional,
                                 "profile": p, "split_union": sorted(ss),
                                 "N2_split_missing": next(iter(base_s - ss))})

    prefix_checks = 0
    for depth in range(5):
        for sequence in permutations(range(5), depth):
            unasked = set(range(5)) - set(sequence)
            compatible_candidates = [c for c in local_candidates
                                     if all(c["profile"][q] == base_p[q] for q in sequence)]
            assert len(compatible_candidates) == 5 - depth
            assert {QUARTETS.index(tuple(c["exceptional_quartet"]))
                    for c in compatible_candidates} == unasked
            prefix_checks += 1
    assert prefix_checks == 206

    dataset = {}
    categories = {}
    for graph in trees(N):
        labels = {x: x for x in range(N)}
        p = distance_profile(graph, labels)
        ss = graph_splits(graph, labels)
        assert p not in dataset
        dataset[p] = ss
    categories["binary_trees"] = len(dataset)
    for name in ("N1", "N2"):
        orbit = {}
        for relabel in permutations(range(N)):
            p, ss, _ = fixture_display(fixtures[name], relabel)
            if p in orbit:
                assert orbit[p] == ss
            orbit[p] = ss
        categories[name + "_orbit"] = len(orbit)
        for p, ss in orbit.items():
            assert p not in dataset
            dataset[p] = ss
    assert categories == {"binary_trees": 15, "N1_orbit": 60, "N2_orbit": 12}
    assert len(dataset) == len(set(dataset.values())) == 87
    circles = [(0,) + tail for tail in permutations(range(1, N)) if tail[0] < tail[-1]]
    for p, ss in dataset.items():
        passing = [c for c in circles if all(circular(s, c) for s in ss)]
        assert passing
        for c in passing:
            for qi, q in enumerate(QUARTETS):
                induced = [x for x in c if x in q]
                alternating = {induced[0], induced[2]}
                forbidden = next(j for j, partner in enumerate(q[1:])
                                 if {q[0], partner} == alternating or set(q) - {q[0], partner} == alternating)
                assert not p[qi] & (1 << forbidden)

    ordered = sorted(dataset)
    dp = minimax(ordered, [dataset[p] for p in ordered])
    assert dp["optimal_worst_case_queries"] == 5
    report = {"status": "PASS", "n": N, "quartets_in_order": QUARTETS,
              "inherited_admission_receipt_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
              "admission_reused_not_rerun": True,
              "profile_construction": "actual graph switchings; integer path-distance quartets",
              "N2_profile": base_p, "N2_split_union": sorted(base_s),
              "five_N1_rotations": local_candidates,
              "all_distinct_query_prefixes_through_depth_four": prefix_checks,
              "orbit_counts": categories, "distinct_profiles": len(dataset),
              "distinct_split_outputs": len(set(dataset.values())),
              "independent_target_aware_minimax": dp,
              "scope": "Exact deterministic n=5 split-plus-order source optimum, under inherited fixture admission. No asymptotic optimum."}
    path = Path(__file__).with_name("finite-minimax-review.json")
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
