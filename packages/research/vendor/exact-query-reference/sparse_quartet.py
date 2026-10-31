"""Exact fixed-order circular split recovery by quartet rectangle emptiness.

Research prototype, 2026-09-30. No statistical model or order recovery is supplied.
Oracle: sorted four-label tuple -> mask of displayed resolved topologies.
Bits 1,2,4 encode ab|cd, ac|bd, ad|bc respectively for a<b<c<d.
Output: nontrivial circular splits (i,j), with side {i+1,...,j}.
Uses only the Python standard library. Run without -O: tests use assertions.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import deque
from functools import lru_cache
from itertools import combinations, product
from typing import Callable, Iterable, Iterator

Quartet = tuple[int, int, int, int]
GapPair = tuple[int, int]
Rectangle = tuple[int, int, int, int]
Oracle = Callable[[Quartet], int]


def candidates(n: int) -> list[GapPair]:
    """All unordered nonadjacent pairs of circular gaps."""
    if n < 4:
        raise ValueError("At least four taxa are required")
    return [(i, j) for i in range(n) for j in range(i+2, n)
            if (i, j) != (0, n-1)]


def seed_rectangles(left: int, right: int) -> Iterator[Rectangle]:
    """Partition nonadjacent pairs of gaps in [left,right), without wrap."""
    if right-left <= 2:
        return
    mid = (left+right)//2
    if left < mid-1:
        yield left, mid-1, mid, right
    if mid+1 < right:
        yield mid-1, mid, mid+1, right
    yield from seed_rectangles(left, mid)
    yield from seed_rectangles(mid, right)


@dataclass(frozen=True)
class Recovery:
    splits: frozenset[GapPair]
    oracle_calls: int
    rectangle_tests: int
    positive_internal_nodes: int
    max_search_depth: int
    cache_size: int


def recover(n: int, oracle: Oracle, *, require_tree_support: bool = True) -> Recovery:
    """Recover the split union under exact support and common-order promises.

    require_tree_support=False permits empty quartet answers when testing
    abstract circular split families. An encountered crossing topology is
    rejected, but absence of such a response is not an order certificate.
    """
    if not isinstance(n, int) or isinstance(n, bool) or n < 4:
        raise ValueError("n must be an integer at least four")
    cache: dict[Quartet, int] = {}
    found: set[GapPair] = set()
    tests = positive_internal = max_depth = 0

    def ask(q: Quartet) -> int:
        if not (0 <= q[0] < q[1] < q[2] < q[3] < n):
            raise AssertionError(f"Not four sorted distinct taxa: {q}")
        if q not in cache:
            mask = oracle(q)
            if not isinstance(mask, int) or isinstance(mask, bool) or mask < 0 or mask > 7:
                raise ValueError(f"Invalid quartet support mask {mask!r}")
            if mask & 2:
                raise ValueError("Oracle contains a topology crossing the supplied order")
            if require_tree_support and mask == 0:
                raise ValueError("A binary displayed-tree family cannot have empty support")
            cache[q] = mask
        return cache[q]

    def visit(rect: Rectangle, depth: int) -> None:
        nonlocal tests, positive_internal, max_depth
        a, b, c, d = rect
        tests += 1
        max_depth = max(max_depth, depth)
        if not ask((a, b, c, d)) & 4:
            return
        width, height = b-a, d-c
        if width == height == 1:
            found.add((a, c))
            return
        positive_internal += 1
        if width >= height:
            mid = (a+b)//2
            visit((a, mid, c, d), depth+1)
            visit((mid, b, c, d), depth+1)
        else:
            mid = (c+d)//2
            visit((a, b, c, mid), depth+1)
            visit((a, b, mid, d), depth+1)

    # The last gap wraps through label zero; these n-3 cells are handled alone.
    for i in range(1, n-2):
        tests += 1
        if ask((0, i, i+1, n-1)) & 1:
            found.add((i, n-1))
    for rect in seed_rectangles(0, n-1):
        visit(rect, 0)
    return Recovery(frozenset(found), len(cache), tests, positive_internal,
                    max_depth, len(cache))


def query_bound(n: int, k: int) -> int:
    if not isinstance(n, int) or isinstance(n, bool) or n < 4:
        raise ValueError("n must be an integer at least four")
    if not isinstance(k, int) or isinstance(k, bool) or k < 0:
        raise ValueError("k must be a nonnegative integer")
    # Exact ceiling of log2(n-1), avoiding floating-point underestimation.
    return 2*n-6 + 4*k*(n-2).bit_length()


def split_support_oracle(n: int, support: Iterable[GapPair]) -> Oracle:
    """Independent direct bipartition-restriction oracle (not range testing)."""
    pairs = tuple(support)
    allowed = set(candidates(n))
    if any(p not in allowed for p in pairs):
        raise ValueError("Support contains a non-candidate split")
    def query(q: Quartet) -> int:
        result = 0
        for i, j in pairs:
            mask = sum((1 << t) for t, label in enumerate(q) if i < label <= j)
            if mask in (3, 12): result |= 1
            elif mask in (5, 10): result |= 2
            elif mask in (9, 6): result |= 4
        return result
    return query


def validate_partition(n: int) -> None:
    covered: set[GapPair] = set()
    rects = list(seed_rectangles(0, n-1))
    assert len(rects) == n-3, (n, len(rects))
    for a, b, c, d in rects:
        assert 0 <= a < b < c < d < n
        cells = {(i,j) for i in range(a,b) for j in range(c,d)}
        assert not covered.intersection(cells)
        covered.update(cells)
    wrap = {(i,n-1) for i in range(1,n-2)}
    assert not covered.intersection(wrap)
    covered.update(wrap)
    assert covered == set(candidates(n))


# Independent graph-generated tests. Root an ordered unrooted tree at tip 0.
@lru_cache(maxsize=None)
def shapes(lo: int, hi: int) -> tuple:
    if hi-lo == 1:
        return (lo,)
    return tuple((a,b) for m in range(lo+1,hi)
                 for a in shapes(lo,m) for b in shapes(m,hi))


def graph_from_shape(shape, tip_count: int) -> dict[int,set[int]]:
    graph: dict[int,set[int]] = {i:set() for i in range(tip_count)}
    next_id = tip_count
    def attach(node):
        nonlocal next_id
        if isinstance(node,int): return node
        v=next_id; next_id += 1; graph[v]=set()
        for child in node:
            u=attach(child); graph[v].add(u); graph[u].add(v)
        return v
    root=attach(shape); graph[0].add(root); graph[root].add(0)
    assert all(len(graph[v]) == (1 if v<tip_count else 3) for v in graph)
    return graph


def all_distances(graph: dict[int,set[int]], tips: int) -> list[list[int]]:
    rows=[]
    for source in range(tips):
        dist={source:0}; todo=deque([source])
        while todo:
            v=todo.popleft()
            for u in graph[v]:
                if u not in dist: dist[u]=dist[v]+1; todo.append(u)
        rows.append([dist[x] for x in range(tips)])
    return rows


def edge_tip_sides(graph: dict[int,set[int]], tips: int) -> list[frozenset[int]]:
    sides=[]
    for u in graph:
        for v in graph[u]:
            if u>v: continue
            seen={u}; todo=[u]
            while todo:
                x=todo.pop()
                for y in graph[x]:
                    if (x==u and y==v) or (x==v and y==u) or y in seen: continue
                    seen.add(y); todo.append(y)
            sides.append(frozenset(x for x in seen if x<tips))
    return sides


def selected_tree_split_union(graph: dict[int,set[int]], copies: list[list[int]]) -> frozenset[GapPair]:
    """Enumerate globally consistent copy selections and actual tree edges."""
    n=len(copies); tips=sum(map(len,copies)); sides=edge_tip_sides(graph,tips)
    result=set()
    for chosen in product(*copies):
        for side in sides:
            taxa={label for label, tip in enumerate(chosen) if tip in side}
            if not 2 <= len(taxa) <= n-2: continue
            transitions=[i for i in range(n) if (i in taxa) != ((i+1)%n in taxa)]
            assert len(transitions)==2, (taxa,transitions)
            result.add(tuple(transitions))
    return frozenset(result)


def physical_quartet_oracle(graph: dict[int,set[int]], copies: list[list[int]]) -> Oracle:
    """Quartets from BFS distances and local occurrence selections, no split list."""
    dist=all_distances(graph,sum(map(len,copies)))
    def query(q: Quartet) -> int:
        support=0
        for a,b,c,d in product(*(copies[x] for x in q)):
            sums=(dist[a][b]+dist[c][d],dist[a][c]+dist[b][d],dist[a][d]+dist[b][c])
            minimum=min(sums)
            winner=[i for i,x in enumerate(sums) if x==minimum]
            assert len(winner)==1, sums
            rest=[x for x in sums if x!=minimum]
            assert rest[0]==rest[1] and minimum<rest[0], sums
            support |= 1 << winner[0]
        return support
    return query
