from itertools import combinations

# Finite truncation tests of the structural construction only, not avoidance.
N = 10
vertices = [(0, 0)] + [(i, s) for i in range(1, N + 1) for s in (0, 1)]
checks = 0
for bits in range(1 << (N - 2)):
    switch = lambda i: (bits >> (i - 1)) & 1
    outgoing = {v: set() for v in vertices}
    incoming = {v: set() for v in vertices}
    def edge(a, b, label):
        outgoing[a].add(b)
        incoming[b].add((a, label))
    for s in (0, 1):
        edge((0, 0), (2, s), 1)
    for i in range(1, N + 1):
        for side in (0, 1):
            if i + 1 <= N:
                edge((i, side), (i + 1, side), 0)
            if i + 2 <= N:
                edge((i, side), (i + 2, side ^ switch(i)), 1)
    assert {v for v in vertices if not incoming[v]} == {(0, 0), (1, 0), (1, 1)}
    for v in vertices:
        if 2 <= v[0]:
            assert sorted(b for _, b in incoming[v]) == [0, 1]
        if v[0] <= N - 2:
            assert len(outgoing[v]) == 2
    triangles = {t for t in combinations(vertices, 3)
                 if t[1] in outgoing[t[0]] and t[2] in outgoing[t[0]] and t[2] in outgoing[t[1]]}
    expected = {((i, s), (i + 1, s), (i + 2, s))
                for i in range(1, N - 1) if not switch(i) for s in (0, 1)}
    assert triangles == expected
    checks += 1
print(f"{checks} exhaustive switch assignments: roots, interior degrees, incoming labels, and all triangles passed")
