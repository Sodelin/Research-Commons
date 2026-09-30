"""Independent graph controls for candidate-order certification.

Generate all labeled binary trees by leaf insertion. Oracle answers come from
graph cuts. Truth uses direct membership transitions on the complete split
union. The verifier queries only pairs of disjoint adjacent cycle edges.
These checks are finite controls for the separate all-size proof.
"""
from itertools import combinations, permutations
from pathlib import Path
import json
import platform
from datetime import datetime, timezone


def edge(u, v):
    return tuple(sorted((u, v)))


def trees(n):
    out = [frozenset((edge(-1, 0), edge(-1, 1), edge(-1, 2)))]
    for leaf in range(3, n):
        node = -(leaf - 1)
        nxt = []
        for graph in out:
            for u, v in graph:
                nxt.append((graph - {edge(u, v)}) | {
                    edge(u, node), edge(v, node), edge(node, leaf)})
        out = nxt
    assert len(set(out)) == len(out)
    return out


def graph_splits(graph, n):
    adj = {}
    for u, v in graph:
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)
    full = (1 << n) - 1
    ans = set()
    for u, v in graph:
        seen, todo = {u}, [u]
        while todo:
            a = todo.pop()
            for b in adj[a]:
                if edge(a, b) == edge(u, v) or b in seen:
                    continue
                seen.add(b)
                todo.append(b)
        side = sum(1 << x for x in seen if 0 <= x < n)
        side = min(side, full ^ side)
        if min(side.bit_count(), n - side.bit_count()) >= 2:
            ans.add(side)
    return ans


def is_circular(side, order):
    return sum(bool(side & (1 << order[i])) !=
               bool(side & (1 << order[(i + 1) % len(order)]))
               for i in range(len(order))) == 2


def topology_bit(quartet, first_pair, qindex):
    a, b, c, d = quartet
    pair = frozenset(first_pair)
    pairs = [(a, b), (a, c), (a, d)]
    for t, x in enumerate(pairs):
        if pair == frozenset(x) or pair == frozenset(set(quartet) - set(x)):
            return 1 << (3 * qindex + t)
    raise AssertionError((quartet, first_pair))


def run(n, all_families):
    graphs = trees(n)
    qs = list(combinations(range(n), 4))
    qindices = {q: i for i, q in enumerate(qs)}
    split_sets = [graph_splits(g, n) for g in graphs]
    universe = sorted(set().union(*split_sets))
    splitindex = {s: i for i, s in enumerate(universe)}
    support = [sum(1 << splitindex[s] for s in ss) for ss in split_sets]
    profiles = []
    for ss in split_sets:
        profile = 0
        for qi, q in enumerate(qs):
            bits = {topology_bit(q, [x for x in q if s & (1 << x)], qi)
                    for s in ss if sum(bool(s & (1 << x)) for x in q) == 2}
            assert len(bits) == 1
            profile |= next(iter(bits))
        profiles.append(profile)
    certificates = []
    for tail in permutations(range(1, n)):
        order = (0,) + tail
        if order[1] > order[-1]:
            continue
        circular = sum(1 << splitindex[s] for s in universe if is_circular(s, order))
        forbidden = 0
        recovery = []
        unique = set()
        gap_count = 0
        for i, j in combinations(range(n), 2):
            a, b = order[i], order[(i + 1) % n]
            c, d = order[j], order[(j + 1) % n]
            if len({a, b, c, d}) != 4:
                continue
            q = tuple(sorted((a, b, c, d)))
            qi = qindices[q]
            unique.add(q)
            gap_count += 1
            forbidden |= topology_bit(q, (a, c), qi)
            side = sum(1 << order[t] for t in range(i + 1, j + 1))
            side = min(side, ((1 << n) - 1) ^ side)
            recovery.append((topology_bit(q, (b, c), qi), 1 << splitindex[side]))
        assert gap_count == n * (n - 3) // 2
        intervals = 0
        for lo in range(1, n):
            side = 0
            for hi in range(lo, n):
                side |= 1 << order[hi]
                intervals |= 1 << side
        certificates.append((circular, forbidden, recovery, len(unique), intervals))
    counts = {"taxa": n, "binary_trees": len(graphs), "circular_orders": len(certificates),
              "families": 0, "family_order_cases": 0, "accepted": 0, "rejected": 0,
              "maximum_unique_queries": max(c[3] for c in certificates),
              "anchored_interval_equivalence_checks": 0}
    anchored_sets = []
    for x, y in combinations(range(1, n), 2):
        tests = []
        for z in range(1, n):
            if z in (x, y):
                continue
            q = tuple(sorted((0, x, y, z)))
            tests.append((z, topology_bit(q, (x, y), qindices[q])))
        anchored_sets.append((x, y, tests))
    if all_families:
        family_cases = range(1, 1 << len(graphs))
        cached_profiles = [0] * (1 << len(graphs))
        cached_support = [0] * (1 << len(graphs))
        def family(mask):
            bit = mask & -mask
            prior = mask ^ bit
            k = bit.bit_length() - 1
            cached_profiles[mask] = cached_profiles[prior] | profiles[k]
            cached_support[mask] = cached_support[prior] | support[k]
            return cached_profiles[mask], cached_support[mask]
    else:
        family_cases = [(i,) for i in range(len(graphs))] + list(combinations(range(len(graphs)), 2))
        def family(indices):
            p = s = 0
            for i in indices:
                p |= profiles[i]
                s |= support[i]
            return p, s
    for f in family_cases:
        profile, actual = family(f)
        counts["families"] += 1
        intersections = []
        for x, y, tests in anchored_sets:
            side = (1 << x) | (1 << y)
            for z, witness in tests:
                if not profile & witness:
                    side |= 1 << z
            intersections.append(side)
        for circular, forbidden, recovery, _, intervals in certificates:
            accepts = not (profile & forbidden)
            truth = not (actual & ~circular)
            assert accepts == truth, (n, f, circular, forbidden)
            c1p_accepts = all(intervals & (1 << side) for side in intersections)
            assert c1p_accepts == truth, (n, f, intersections, intervals)
            counts["anchored_interval_equivalence_checks"] += 1
            counts["family_order_cases"] += 1
            counts["accepted" if accepts else "rejected"] += 1
            if accepts:
                found = 0
                for witness, split in recovery:
                    if profile & witness:
                        found |= split
                assert found == actual, (n, f, found, actual)
    return counts


if __name__ == "__main__":
    report = {"status": "PASS", "timestamp_utc": datetime.now(timezone.utc).isoformat(),
              "python": platform.python_version(),
              "scope": "all nonempty families of binary 4/5-taxon trees; all singleton/pair families of 6-taxon trees",
              "rows": [run(4, True), run(5, True), run(6, False)],
              "limits": "Finite controls, not an all-size proof, source-admission census or unknown-order algorithm."}
    Path(__file__).with_name("candidate-order-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
