"""Exact graph controls for the three-resolution nonadaptive order obstruction.

Independent of the inherited quartet/support implementation.  Ordinary Python,
integer graph cuts, and exhaustive circles at n <= 7; no statistical premise.
"""

from itertools import combinations, permutations
from collections import deque
import json
from pathlib import Path


def pendant_tree(n, triple, cherry):
    graph = {v: set() for v in range(n)}
    next_vertex = n

    def vertex():
        nonlocal next_vertex
        v = next_vertex
        next_vertex += 1
        graph[v] = set()
        return v

    def edge(a, b):
        graph[a].add(b)
        graph[b].add(a)

    a, b = cherry
    c = next(v for v in triple if v not in cherry)
    v, w = vertex(), vertex()
    edge(w, a)
    edge(w, b)
    edge(v, w)
    edge(v, c)
    outside = [z for z in range(n) if z not in triple]

    def outside_root(leaves):
        if len(leaves) == 1:
            return leaves[0]
        u = vertex()
        edge(u, leaves[0])
        edge(u, outside_root(leaves[1:]))
        return u

    edge(v, outside_root(outside))
    assert all(len(graph[z]) == 1 for z in range(n))
    assert all(len(graph[z]) == 3 for z in graph if z >= n)
    assert sum(map(len, graph.values())) // 2 == len(graph) - 1
    reached = set()
    queue = [0]
    while queue:
        z = queue.pop()
        if z in reached:
            continue
        reached.add(z)
        queue.extend(graph[z] - reached)
    assert reached == set(graph)
    return graph


def distances(graph, n):
    result = {}
    for start in range(n):
        dist = {start: 0}
        queue = deque([start])
        while queue:
            v = queue.popleft()
            for w in graph[v]:
                if w not in dist:
                    dist[w] = dist[v] + 1
                    queue.append(w)
        result[start] = dist
    return result


def quartet(dist, taxa):
    a, b, c, d = taxa
    sums = (dist[a][b] + dist[c][d],
            dist[a][c] + dist[b][d],
            dist[a][d] + dist[b][c])
    small = min(sums)
    assert sums.count(small) == 1
    return sums.index(small)


def tree_splits(graph, n):
    answer = set()
    for v in graph:
        for w in graph[v]:
            if v >= w:
                continue
            seen = set()
            queue = [v]
            while queue:
                z = queue.pop()
                if z in seen:
                    continue
                seen.add(z)
                queue.extend(q for q in graph[z] - seen if not (z == v and q == w))
            side = frozenset(z for z in seen if z < n)
            complement = frozenset(range(n)) - side
            if len(side) > 1 and len(complement) > 1:
                answer.add(min((tuple(sorted(side)), tuple(sorted(complement)))))
    return answer


def compatible(circle, splits):
    n = len(circle)
    for side in splits:
        side = set(side)
        changes = sum((circle[i] in side) != (circle[(i + 1) % n] in side)
                      for i in range(n))
        if changes != 2:
            return False
    return True


def main():
    report = {"status": "PASS", "graph_family": "binary pendant triple trees",
              "taxon_sizes": list(range(4, 10)), "triple_witnesses": 0,
              "quartet_comparisons": 0, "different_quartets": 0,
              "circles_checked": 0, "all_three_common_circles": 0,
              "per_size": []}
    for n in range(4, 10):
        local = {"n": n, "triples": 0, "quartets": 0, "circles": 0}
        circles = None
        if n <= 7:
            circles = [(0,) + p for p in permutations(range(1, n)) if p[0] < p[-1]]
        for triple in combinations(range(n), 3):
            graphs = [pendant_tree(n, triple, pair) for pair in combinations(triple, 2)]
            ds = [distances(g, n) for g in graphs]
            ss = [tree_splits(g, n) for g in graphs]
            for q in combinations(range(n), 4):
                answers = [quartet(d, q) for d in ds]
                hidden = set(triple).issubset(q)
                assert (len(set(answers)) == 3) if hidden else (len(set(answers)) == 1)
                report["quartet_comparisons"] += 1
                report["different_quartets"] += int(hidden)
                local["quartets"] += 1
            if circles is not None:
                for circle in circles:
                    accepted = [compatible(circle, s) for s in ss]
                    assert not all(accepted)
                    report["circles_checked"] += 1
                    local["circles"] += 1
            report["triple_witnesses"] += 1
            local["triples"] += 1
        report["per_size"].append(local)
    path = Path(__file__).with_name("adaptive-adversary-controls.json")
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
