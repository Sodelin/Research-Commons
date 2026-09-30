"""Independent finite controls for Astra's pinned weighted query accounting.

Contributor: Codex algebra-audit, ASTRA-QUERY-REVIEW-20260930.
Run against an exported 836cc5a62648f72e59161d583f882b12ac801495 provider
directory containing adaptive_order.py, core.py and insertion.py. Tests are
controls, not an all-size proof or a full frontier-language verification.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import sys

PIN = '836cc5a62648f72e59161d583f882b12ac801495'
EXPECTED = {
    'adaptive_order.py': '5ac90d944e104d79d893fb266342806e565bfad9',
    'core.py': '2d679d1f284889fb754f2475d6d7c0ec7de47421',
    'insertion.py': '88c0b7dd1027d48ebcce6f6d9382602377f3d462',
}


def git_blob(path):
    data = path.read_bytes()
    return hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()


def path_nodes(adj, start, end):
    parent = {start: None}
    todo = [start]
    for v in todo:
        if v == end:
            break
        for u in adj[v]:
            if u not in parent:
                parent[u] = v
                todo.append(u)
    ans = set()
    v = end
    while v is not None:
        ans.add(v)
        v = parent[v]
    return ans


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--provider-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    hashes = {f: git_blob(args.provider_dir / f) for f in EXPECTED}
    assert hashes == EXPECTED, (hashes, EXPECTED)
    sys.path.insert(0, str(args.provider_dir))
    from adaptive_order import AdaptiveOrderLearner, CircularTree
    from core import pair_bit

    counts = Counter()
    rng = random.Random(20260930)
    max_corner_queries = 0
    max_arrow_queries = 0

    def local_control(weights, mode, position, port_order=None):
        nonlocal max_corner_queries, max_arrow_queries
        d = len(weights)
        ports = list(range(d)) if port_order is None else list(port_order)
        z = d + 10
        truth = set((position - 1, position)) if mode == 'arrow' else {position}
        full = ports[:position + 1] + [z] + ports[position + 1:]

        def oracle(q):
            if mode == 'arrow' and ports[position] in q:
                return pair_bit(q, (z, ports[position]))
            restricted = [x for x in full if x in q]
            return 7 ^ pair_bit(q, (restricted[0], restricted[2]))

        learner = AdaptiveOrderLearner(ports, oracle)
        learner.tree.rot = {-1: ports.copy(), **{p: [-1] for p in ports}}
        learner.tree.taxa = set(ports)
        learner.z = z
        result = learner.biased_classify(-1, dict(zip(ports, weights)))
        calls = learner.stats['biased_predicates']
        W = sum(weights)
        if mode == 'arrow':
            assert result == ports[position], (weights, mode, position, result)
            assert weights[position] > 0
            bound = 2 + 4 * math.log2(W / weights[position])
            max_arrow_queries = max(max_arrow_queries, calls)
        else:
            assert result is None, (weights, mode, position, result)
            bound = 2 + 4 * math.log2(max(1, W))
            max_corner_queries = max(max_corner_queries, calls)
        assert calls <= bound + 1e-10, (weights, mode, position, calls, bound)
        # Replay independently: every exact truth gap survives every query.
        for q, answer in learner.cache.items():
            cuts = sorted(ports.index(x) for x in q if x != z)
            a, b, c = cuts
            forbidden = (pair_bit(q, (z, ports[c])),
                         pair_bit(q, (z, ports[a])),
                         pair_bit(q, (z, ports[b])))
            for g in truth:
                g %= d
                arc = 0 if a <= g < b else 1 if b <= g < c else 2
                assert not (answer & forbidden[arc]), (weights, mode, position, q, answer, g)
        counts[f'local_{mode}'] += 1

    for d in range(3, 7):
        for weights in itertools.product(range(3), repeat=d):
            for position in range(d):
                local_control(weights, 'corner', position)
                if weights[position]:
                    local_control(weights, 'arrow', position)
    for d in list(range(7, 33)) + [64, 128, 257]:
        for _ in range(40):
            ports = list(range(d))
            rng.shuffle(ports)
            weights = [rng.choice([0, 0, 1, 1, 2, 7, 1000]) for _ in range(d)]
            for position in rng.sample(range(d), min(d, 6)):
                local_control(weights, 'corner', position, ports)
                if weights[position]:
                    local_control(weights, 'arrow', position, ports)
        # Balanced uniform weights, with heavy cuts crossing the index boundary.
        for weights in ([1] * d, [0, 0] + [1] * (d - 2), [100000] + [1] * (d - 1)):
            for position in (0, 1, d - 1):
                local_control(weights, 'corner', position)
                if weights[position]:
                    local_control(weights, 'arrow', position)

    # Real binary-tree-family oracles for centroid search, including pendant
    # attachment edges and paths touching the search-region boundary.
    for m in range(3, 33):
        for _ in range(16):
            B = CircularTree((0, 1, 2))
            for old_z in range(3, m):
                edges = [(u, v) for u in B.rot for v in B.rot[u] if u < v]
                B.subdivide(*rng.choice(edges), old_z)
            edges = [(u, v) for u in B.rot for v in B.rot[u] if u < v]
            choices = [(edge,) for edge in rng.sample(edges, min(4, len(edges)))]
            choices += [tuple(rng.sample(edges, 2)) for _ in range(4)]
            for positions in choices:
                z = m + 10
                family = []
                for u, v in positions:
                    adj = {x: ns.copy() for x, ns in B.rot.items()}
                    t = min(adj) - 1
                    adj[u][adj[u].index(v)] = t
                    adj[v][adj[v].index(u)] = t
                    adj[t] = [u, v, z]
                    adj[z] = [t]
                    family.append(adj)

                def oracle(q):
                    mask = 0
                    a = q[0]
                    for adj in family:
                        for b in q[1:]:
                            c, d = [x for x in q if x not in (a, b)]
                            if path_nodes(adj, a, b).isdisjoint(path_nodes(adj, c, d)):
                                mask |= pair_bit(q, (a, b))
                    assert mask in (1, 2, 3, 4, 5, 6)
                    return mask

                learner = AdaptiveOrderLearner(tuple(range(m)), oracle)
                learner.tree = B
                learner.z = z
                located = learner.find_central()
                if len(positions) == 1:
                    assert located[0] == 'edge' and set(located[1:]) == set(positions[0]), (m, positions, located)
                    counts['centroid_exceptional_edge'] += 1
                    counts['centroid_pendant_edge'] += any(v in B.taxa for v in positions[0])
                else:
                    corner_vertices = set()
                    for v in set(B.rot) - B.taxa:
                        branches = [B.component(u, v) for u in B.rot[v]]
                        if not any(all(set(edge) <= branch | {v} for edge in positions) for branch in branches):
                            corner_vertices.add(v)
                    assert located[0] == 'vertex' and located[1] in corner_vertices, (m, positions, located, corner_vertices)
                    counts['centroid_corner_path'] += 1
                calls = learner.stats['biased_predicates'] + learner.stats['arrow_predicates']
                assert calls <= 7 * math.ceil(math.log2(2 * m)) + 2

    result = {'status': 'PASS', 'claim_class': 'independent finite controls',
              'source_commit': PIN, 'provider_git_blobs': hashes,
              'seed': 20260930, 'counts': dict(counts),
              'maximum_local_corner_predicates': max_corner_queries,
              'maximum_local_arrow_predicates': max_arrow_queries,
              'limits': 'Not a formal proof or a full all-family frontier-language verification.'}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
