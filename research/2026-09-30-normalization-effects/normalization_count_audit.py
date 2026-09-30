"""Finite graph checks for port-compressed reticulation count extremizers.

Contributor: Codex normalization-count subagent, 2026-09-30.
No coalescent/CF computation or preservation theorem is implemented here.
Planarity is established in the written exterior-cycle construction, not by
this script. This independently checks binary DAG/LSA, blobs, and counts.
"""
from collections import defaultdict, deque
import json


def skeleton(q, prefix):
    us = [prefix + 'U' + str(i) for i in range(q)]
    if q == 2:
        pairs = [(us[0], us[1])]
    elif q == 3:
        c = prefix + 'C'
        pairs = [(c, u) for u in us]
    elif q == 4:
        v, w = prefix + 'V', prefix + 'W'
        pairs = [(v, us[0]), (v, us[1]), (v, w), (w, us[2]), (w, us[3])]
    elif q == 5:
        v, m, w = prefix + 'V', prefix + 'M', prefix + 'W'
        pairs = [(v, us[0]), (v, us[1]), (v, m), (m, us[2]),
                 (m, w), (w, us[3]), (w, us[4])]
    else:
        raise ValueError(q)
    return us, pairs


def orient(edges, start):
    adj = defaultdict(list)
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    result, seen, queue = [], {start}, deque([start])
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
                result.append((u, v))
    return result


def root_blob(q):
    prefix = 'b0_'
    us, tree = skeleton(q, prefix)
    edge = next((e for e in tree if all('U' not in v for v in e)), tree[0])
    tree.remove(edge)
    tree.extend([('R', edge[0]), ('R', edge[1])])
    edges = orient(tree, 'R')
    hybrids, leaves = [], []
    for i in range(q):
        h, x = prefix + 'H' + str(i), prefix + 'X' + str(i)
        hybrids.append(h)
        leaves.append(x)
        edges.extend([(us[i], h), (us[(i + 1) % q], h), (h, x)])
    return edges, hybrids, leaves


def graft(edges, hybrids, leaves, q, index):
    old = leaves.pop()
    incoming = next(e for e in edges if e[1] == old)
    edges.remove(incoming)
    prefix = 'b' + str(index) + '_'
    us, tree = skeleton(q, prefix)
    entry = prefix + 'ENTRY'
    edges.extend([(incoming[0], entry), (entry, us[0])])
    edges.extend(orient(tree, us[0]))
    for i in range(q):
        h, x = prefix + 'H' + str(i), prefix + 'X' + str(i)
        hybrids.append(h)
        leaves.append(x)
        parent = entry if i == 0 else us[i]
        edges.extend([(parent, h), (us[(i + 1) % q], h), (h, x)])


def check(edges, hybrids, leaves):
    parents, children = defaultdict(list), defaultdict(list)
    for u, v in edges:
        parents[v].append(u)
        children[u].append(v)
    vertices = set(parents) | set(children)
    for v in vertices:
        degree = (len(parents[v]), len(children[v]))
        expected = (0, 2) if v == 'R' else ((2, 1) if v in hybrids
                   else ((1, 0) if v in leaves else (1, 2)))
        assert degree == expected, (v, degree, expected)
    indeg = {v: len(parents[v]) for v in vertices}
    queue, order = deque(['R']), []
    while queue:
        u = queue.popleft()
        order.append(u)
        for v in children[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                queue.append(v)
    assert len(order) == len(vertices), 'Not an acyclic root-connected graph'
    dom = {'R': {'R'}}
    for v in order[1:]:
        common = set.intersection(*(dom[p] for p in parents[v]))
        dom[v] = common | {v}
    assert set.intersection(*(dom[x] for x in leaves)) == {'R'}, 'Root not LSA'

    # Undirected bridges, retaining the subdividing root in its original blob.
    adj = defaultdict(list)
    for eid, (u, v) in enumerate(edges):
        adj[u].append((v, eid))
        adj[v].append((u, eid))
    discovery, low, bridges, time = {}, {}, set(), [0]

    def visit(u, parent_edge=-1):
        discovery[u] = low[u] = time[0]
        time[0] += 1
        for v, eid in adj[u]:
            if eid == parent_edge:
                continue
            if v in discovery:
                low[u] = min(low[u], discovery[v])
            else:
                visit(v, eid)
                low[u] = min(low[u], low[v])
                if low[v] > discovery[u]:
                    bridges.add(eid)

    visit('R')
    components, seen = [], set()
    for initial in vertices:
        if initial in seen:
            continue
        component, queue = set(), deque([initial])
        seen.add(initial)
        while queue:
            u = queue.popleft()
            component.add(u)
            for v, eid in adj[u]:
                if eid not in bridges and v not in seen:
                    seen.add(v)
                    queue.append(v)
        hcount = sum(h in component for h in hybrids)
        if hcount:
            ports = sum((u in component) != (v in component)
                        for eid, (u, v) in enumerate(edges) if eid in bridges)
            components.append({'hybrids': hcount, 'ports': ports,
                               'contains_root': 'R' in component})
    return {'n': len(leaves), 'r': len(hybrids), 'vertices': len(vertices),
            'edges': len(edges), 'blobs': sorted(components,
             key=lambda x: (not x['contains_root'], x['ports']))}


def run():
    results = []
    for n in range(4, 21):
        edges, hybrids, leaves = root_blob(3)
        for i in range(1, n - 2):
            graft(edges, hybrids, leaves, 2, i)
        result = check(edges, hybrids, leaves)
        assert result['n'] == n and result['r'] == 2 * n - 3
        assert all(b['ports'] == 3 for b in result['blobs'])
        result['normalization'] = 'delete_two_port_blobs'
        results.append(result)

        q = 4 if n % 2 == 0 else 5
        edges, hybrids, leaves = root_blob(q)
        for i in range(1, (n - q) // 2 + 1):
            graft(edges, hybrids, leaves, 3, i)
        result = check(edges, hybrids, leaves)
        assert result['n'] == n and result['r'] == (3 * n) // 2 - 2
        assert all(b['ports'] >= 4 for b in result['blobs'])
        result['normalization'] = 'delete_two_and_three_port_blobs'
        results.append(result)
    return {'status': 'passed', 'instances': len(results),
            'checked': ['binary degrees', 'acyclicity', 'root connectivity',
                        'root LSA via dominators', 'bridge-defined blobs',
                        'port counts', 'extremal reticulation counts'],
            'not_checked': ['algorithmic planarity', 'quartet CFs',
                            'coalescent replacement', 'minimum realization'],
            'results': results}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
