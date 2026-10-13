"""Own exact finite witness validation; not a Lean or native admission run.
Usage: python3 -I -B check_admission_witnesses.py [ADMISSION-WITNESSES.json]
"""
from pathlib import Path
from fractions import Fraction as F
import json
import sys

p = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name('ADMISSION-WITNESSES.json')
w = json.loads(p.read_text())
c = w['code']
s, t, leaf = c['source'], c['target'], c['leaf']
assert c['vertex_count'] == 2*4+2*1-1 == 9
assert c['edge_count'] == 2*4+3*1-2 == 9
assert len(s) == len(t) == 9 and len(set(leaf)) == 4
assert c['root'] == 0 and c['site'] == [4]
assert c['parent_false'] == [3] and c['parent_true'] == [4]
assert t[3] == t[4] == 4 and 3 != 4
for v in range(9):
    inc = [e for e in range(9) if t[e] == v]
    out = [e for e in range(9) if s[e] == v]
    assert w['degree_fibres'][v] == {'vertex': v, 'incoming': inc, 'outgoing': out}
    expected = (0, 2) if v == 0 else (1, 0) if v in leaf else (2, 1) if v == 4 else (1, 2)
    assert (len(inc), len(out)) == expected
rank = w['strict_descent_rank']
assert all(rank[s[e]] > rank[t[e]] for e in range(9))

def directed_path(edges):
    at, vertices = 0, [0]
    for e in edges:
        assert s[e] == at
        at = t[e]
        vertices.append(at)
    return vertices

for v, edges in w['root_paths'].items():
    assert directed_path(edges)[-1] == int(v)
assert sorted(x['blocked_vertex'] for x in w['lsa_avoiding_paths']) == list(range(1, 9))
for x in w['lsa_avoiding_paths']:
    path = directed_path(x['edge_path'])
    assert x['blocked_vertex'] not in path
    assert path[-1] == x['leaf_vertex'] == leaf[x['leaf_taxon']]
for eid, vertices in w['bridge_target_components'].items():
    e, side = int(eid), set(vertices)
    assert s[e] not in side and t[e] in side
    assert all((s[f] in side) == (t[f] in side) for f in range(9) if f != e)
for eid, detour in w['nonbridge_detours'].items():
    e = int(eid)
    assert len(detour) == 1
    f = detour[0]
    assert e != f and (s[e], t[e]) == (s[f], t[f])
assert [e for e in range(9) if s[e] == 4] == [5]
print('PASS: Code counts, degree fibres, exact singleton registry and parent IDs')
print('PASS: strict acyclic rank, all root paths and all endpoint-inclusive LSA avoiding paths')
print('PASS: all bridge cut partitions, parallel detours and literal CutChild requirement')

emb = w['outer_embedding']
pt = [tuple(map(F, a)) for a in emb['vertex_coordinates']]
assert len(set(pt)) == 9
polys = []
for e in range(9):
    mids = [tuple(map(F, a)) for a in emb['edge_interior_waypoints'].get(str(e), [])]
    polys.append([pt[s[e]]] + mids + [pt[t[e]]])

def cross(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])

def on(a, b, p):
    return cross(a, b, p) == 0 and all(min(a[i], b[i]) <= p[i] <= max(a[i], b[i]) for i in [0, 1])

def intersection(a, b, c, d):
    o = [cross(a, b, c), cross(a, b, d), cross(c, d, a), cross(c, d, b)]
    if o[0]*o[1] > 0 or o[2]*o[3] > 0:
        return set()
    endpoints = {p for p in [a, b, c, d] if on(a, b, p) and on(c, d, p)}
    if all(x == 0 for x in o):
        assert len(endpoints) <= 1, 'positive collinear overlap'
        return endpoints
    if endpoints:
        return endpoints
    raise AssertionError('proper crossing')

segments = [(e, i, line[i], line[i+1]) for e, line in enumerate(polys) for i in range(len(line)-1)]
for e, i, a, b in segments:
    assert a != b and min(a[1], b[1]) >= 0
    assert all(not on(a, b, pt[v]) for v in range(9) if v not in [s[e], t[e]])
for j, (e, i, a, b) in enumerate(segments):
    for f, h, q, r in segments[j+1:]:
        hits = intersection(a, b, q, r)
        allowed = {pt[v] for v in {s[e], t[e]} & {s[f], t[f]}} if e != f else {a, b} & {q, r}
        assert hits <= allowed
assert all(pt[v][1] == 0 for v in leaf)
assert len({pt[v][0] for v in leaf}) == 4
print('PASS: rational polygonal edges have no interior crossings or hidden vertex incidences')
print('PASS: all four leaves access the same empty lower half-plane; hand outer-face witness')
print('LIMIT: exact finite-data validation only; no Lean proof term, compiler or native job')
