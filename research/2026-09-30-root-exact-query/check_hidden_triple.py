"""Finite controls for the admitted-tree nonadaptive lower-bound witness."""
from collections import deque
from itertools import combinations
import json

def build(taxa, trio, cherry):
    g = {}
    count = 0
    def node():
        nonlocal count
        count += 1
        return ('v', count)
    def edge(a, b):
        g.setdefault(a, set()).add(b)
        g.setdefault(b, set()).add(a)
    def rooted(ls):
        if len(ls) == 1:
            return ls[0]
        r = node()
        edge(r, ls[0])
        edge(r, rooted(ls[1:]))
        return r
    root, c = node(), node()
    edge(root, c)
    for t in cherry:
        edge(c, t)
    edge(root, next(t for t in trio if t not in cherry))
    edge(root, rooted([t for t in taxa if t not in trio]))
    assert all(len(g[t]) == 1 for t in taxa)
    assert all(len(adj) == 3 for v, adj in g.items() if v not in taxa)
    d = {}
    for t in taxa:
        dist = {t: 0}
        pending = deque([t])
        while pending:
            v = pending.popleft()
            for w in g[v]:
                if w not in dist:
                    dist[w] = dist[v]+1
                    pending.append(w)
        for u in taxa:
            d[t,u] = dist[u]
    return d

def quartet(d, q):
    a,b,c,e = q
    values = [d[a,b]+d[c,e], d[a,c]+d[b,e], d[a,e]+d[b,c]]
    best = min(values)
    assert values.count(best) == 1
    return values.index(best)

instances = queries = differing = 0
for n in range(4,9):
    taxa = list(range(n))
    for trio in combinations(taxa,3):
        a,b,c = trio
        d1 = build(taxa,trio,(a,b))
        d2 = build(taxa,trio,(a,c))
        instances += 1
        for q in combinations(taxa,4):
            actual = quartet(d1,q) != quartet(d2,q)
            expected = set(trio).issubset(q)
            assert actual == expected, (n,trio,q)
            queries += 1
            differing += actual
print(json.dumps({'status':'PASS','n_values':list(range(4,9)),
                  'admitted_tree_pairs':instances,'quartet_comparisons':queries,
                  'differing_quartets':differing,
                  'scope':'Finite controls; all-size proof is in LOWER-BOUND.md'},indent=2))
