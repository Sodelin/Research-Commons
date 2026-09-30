"""Exact graph and bitset helpers for independent adaptive-adversary controls."""

from itertools import combinations


def canonical(side, n):
    return min(side, ((1 << n) - 1) ^ side)


def trees(n):
    family = [{0: {n}, 1: {n}, 2: {n}, n: {0, 1, 2}}]
    for taxon in range(3, n):
        grown = []
        internal = n + taxon - 2
        for graph in family:
            for a in graph:
                for b in graph[a]:
                    if a >= b:
                        continue
                    new = {v: set(neighbors) for v, neighbors in graph.items()}
                    new[a].remove(b)
                    new[b].remove(a)
                    new[a].add(internal)
                    new[b].add(internal)
                    new[internal] = {a, b, taxon}
                    new[taxon] = {internal}
                    grown.append(new)
        family = grown
    for graph in family:
        assert all(len(graph[z]) == 1 for z in range(n))
        assert all(len(graph[z]) == 3 for z in graph if z >= n)
        assert sum(map(len, graph.values())) // 2 == len(graph) - 1
    return family


def splits(graph, n):
    answer = set()
    for a in graph:
        for b in graph[a]:
            if a >= b:
                continue
            seen = set()
            queue = [a]
            while queue:
                z = queue.pop()
                if z in seen:
                    continue
                seen.add(z)
                queue.extend(v for v in graph[z] - seen if not (z == a and v == b))
            side = canonical(sum(1 << z for z in seen if z < n), n)
            if 2 <= side.bit_count() <= n - 2:
                answer.add(side)
    assert len(answer) == n - 3
    return answer


def circular(side, circle):
    n = len(circle)
    return sum(bool(side & (1 << circle[i])) != bool(side & (1 << circle[(i + 1) % n]))
               for i in range(n)) == 2


def quartet_support(graph, n, quartets=None):
    if quartets is None:
        quartets = list(combinations(range(n), 4))
    ss = splits(graph, n)
    result = 0
    for p, q in enumerate(quartets):
        a, b, c, d = q
        partitions = ({a, b}, {a, c}, {a, d})
        found = set()
        for s in ss:
            side = {z for z in q if s & (1 << z)}
            if len(side) != 2:
                continue
            for j, part in enumerate(partitions):
                if side == part or set(q) - side == part:
                    found.add(j)
        assert len(found) == 1
        result |= 1 << (3 * p + found.pop())
    return result
