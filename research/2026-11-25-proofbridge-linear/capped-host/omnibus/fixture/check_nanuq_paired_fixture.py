#!/usr/bin/env python3
"""Exact, dependency-free replay of NANUQ-Paired-Fixture.json."""
from collections import defaultdict, deque
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
import re

fixture = json.loads(Path(__file__).with_name("NANUQ-Paired-Fixture.json").read_text())
blocks = fixture["label_blocks"]
labels = sorted(blocks)
contour = fixture["plane_tip_contour"]

def parse(newick):
    compact = "".join(newick.split())
    tokens = iter(re.findall(r"[A-Za-z][A-Za-z0-9]*|[(),;]", compact))
    def walk(token):
        if token != "(":
            assert token.isalnum()
            return token
        left = walk(next(tokens))
        assert next(tokens) == ","
        right = walk(next(tokens))
        assert next(tokens) == ")"
        return left, right
    result = walk(next(tokens))
    assert next(tokens) == ";" and next(tokens, None) is None
    return result

def flatten(tree):
    return [tree] if isinstance(tree, str) else [x for child in tree for x in flatten(child)]

def split(x, y):
    return "|".join(sorted(("".join(sorted(x)), "".join(sorted(y)))))

def run(key):
    rooted = parse(fixture[key])
    assert rooted[1] == "e" and flatten(rooted) == contour
    assert [x for label in labels for x in blocks[label]] == contour
    assert all(len(bl) in (1, 2) for bl in blocks.values())
    graph = defaultdict(set)
    def visit(t):
        if isinstance(t, str):
            return t
        a, b = map(visit, t)
        graph[t] |= {a, b}
        graph[a].add(t)
        graph[b].add(t)
        return t
    visit(rooted)
    a, b = rooted
    graph[a].remove(rooted)
    graph[b].remove(rooted)
    graph[a].add(b)
    graph[b].add(a)
    del graph[rooted]
    assert set(v for v in graph if len(graph[v]) == 1) == set(contour)
    assert all(len(graph[v]) == (1 if isinstance(v, str) else 3) for v in graph)
    assert sum(map(len, graph.values())) == 2 * (len(graph) - 1)
    def distances(start):
        result = {start: 0}
        q = deque([start])
        while q:
            v = q.popleft()
            for w in graph[v] - result.keys():
                result[w] = result[v] + 1
                q.append(w)
        assert len(result) == len(graph)
        return result
    ds = {v: distances(v) for v in graph}
    edges = [(v, w) for v in graph for w in graph[v] if repr(v) < repr(w)]
    support, families, individual = defaultdict(set), set(), []
    for choices in product(*(blocks[label] for label in labels)):
        tip = dict(zip(labels, choices))
        for i, j, k, l in combinations(labels, 4):
            scores = sorted(
                (ds[tip[x]][tip[y]] + ds[tip[z]][tip[w]], split(x+y, z+w))
                for x, y, z, w in [(i,j,k,l), (i,k,j,l), (i,l,j,k)]
            )
            assert scores[0][0] < scores[1][0] == scores[2][0]
            support[i+j+k+l].add(scores[0][1])
        selected = set()
        for v,w in edges:
            side = {label for label in labels if ds[v][tip[label]] < ds[w][tip[label]]}
            if 1 < len(side) < len(labels)-1:
                selected.add(split(side, set(labels)-side))
        assert len(selected) == 2
        individual.append([*choices[:2], sorted(selected)])
        families.add(frozenset(selected))
    assert individual == fixture[key+"_selection_splits"]
    assert {q:sorted(s) for q,s in support.items()} == fixture["distinct_quartet_support"]
    return support, families

def matrix(support):
    result = [[Fraction(0) for _ in labels] for _ in labels]
    for i,j in combinations(range(len(labels)),2):
        x,y=labels[i],labels[j]
        separation = Fraction(0)
        for z,w in combinations([v for v in labels if v not in (x,y)],2):
            values=support["".join(sorted(x+y+z+w))]
            separation += Fraction(sum(not any(x in s and y in s for s in r.split("|")) for r in values),len(values))
        result[i][j]=result[j][i]=2*separation+2*len(labels)-4
    assert all(value.denominator == 1 for row in result for value in row)
    return [[int(value) for value in row] for row in result]

SA, FA = run("A")
SB, FB = run("B")
assert SA == SB
assert set().union(*FA) == set().union(*FB)
assert len(FA) == 3 and len(FB) == 2 and FB < FA
assert FA-FB == {frozenset(fixture["full_tree_split_pair_A_only"])}
D = matrix(SA)
assert D == matrix(SB)
print("PASS: exact support and split union match; full trees differ (3 vs 2).")
print(json.dumps({"labels":labels,"common_raw_distance":D}))
