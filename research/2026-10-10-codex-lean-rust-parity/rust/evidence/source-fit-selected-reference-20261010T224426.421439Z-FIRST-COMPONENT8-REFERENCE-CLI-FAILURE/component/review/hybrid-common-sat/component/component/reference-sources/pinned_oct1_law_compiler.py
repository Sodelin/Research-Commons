"""Exact unranked coalescent laws on supplied finite binary rooted DAGs.

This is a forward-law compiler, NOT an all-source census or an admission
checker for the Commons outer-labeled planar cut-child galled class.
Distinct edge indices preserve parallel arcs. No numerical approximation.
Requires Python >=3.10 and SymPy. Complexity is intentionally exponential.
"""
from __future__ import annotations
from collections import defaultdict, deque
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, product
from math import comb, prod
from typing import Mapping
import sympy as sp

Tree = str | tuple
Forest = tuple[Tree, ...]


def forest(ts) -> Forest:
    return tuple(sorted(ts, key=repr))


@lru_cache(maxsize=None)
def merge_levels(start: Forest) -> tuple:
    """For each lineage count: exact number of ordered pair-merger paths."""
    levels = [(len(start), {start: 1})]
    while levels[-1][0] > 1:
        k, states = levels[-1]
        nxt = defaultdict(int)
        for fs, count in states.items():
            for i, j in combinations(range(k), 2):
                joined = tuple(sorted((fs[i], fs[j]), key=repr))
                out = forest([v for h, v in enumerate(fs) if h not in (i, j)] + [joined])
                nxt[out] += count
        levels.append((k - 1, dict(nxt)))
    return tuple((k, tuple(d.items())) for k, d in levels)


def path_polynomial(k: int, j: int, x):
    """Probability of a specified ordered k-to-j merger path by edge end."""
    if not (1 <= j <= k):
        raise ValueError('Require 1 <= j <= k.')
    rates = [comb(h, 2) for h in range(j, k + 1)]
    return sp.Add(*(sp.Rational(1, prod(b - a for b in rates if b != a)) * x**a
                    for a in rates))


@lru_cache(maxsize=None)
def edge_kernel(start: Forest, x) -> tuple:
    if not start:
        return (((), sp.S.One),)
    ans = []
    for j, states in merge_levels(start):
        h = path_polynomial(len(start), j, x)
        ans.extend((fs, count * h) for fs, count in states)
    return tuple(ans)


def root_kernel(start: Forest) -> tuple:
    if not start:
        raise ValueError('An ancestral population needs at least one sampled lineage.')
    states = merge_levels(start)[-1][1]
    den = prod(comb(h, 2) for h in range(2, len(start) + 1))
    return tuple((fs[0], sp.Rational(count, den)) for fs, count in states)


@dataclass(frozen=True)
class Network:
    edges: tuple[tuple[str, str], ...]
    root: str
    leaves: tuple[str, ...]

    def structure(self):
        if not self.edges or len(set(self.leaves)) != len(self.leaves):
            raise ValueError('Need edges and unique taxon labels.')
        nodes = set(sum((list(e) for e in self.edges), []))
        if self.root not in nodes or not set(self.leaves) <= nodes:
            raise ValueError('Root/leaves missing from graph.')
        incoming = {v: [] for v in nodes}
        outgoing = {v: [] for v in nodes}
        for i, (u, v) in enumerate(self.edges):
            incoming[v].append(i)
            outgoing[u].append(i)
        hybrids = []
        for v in nodes:
            deg = (len(incoming[v]), len(outgoing[v]))
            if v == self.root:
                good = deg == (0, 2)
            elif v in self.leaves:
                good = deg == (1, 0)
            else:
                good = deg in ((1, 2), (2, 1))
                if deg == (2, 1):
                    hybrids.append(v)
            if not good:
                raise ValueError(f'Invalid binary degree at {v}: {deg}')
        remaining = {v: len(incoming[v]) for v in nodes}
        ready = deque([self.root])
        order = []
        while ready:
            v = ready.popleft()
            order.append(v)
            for e in outgoing[v]:
                child = self.edges[e][1]
                remaining[child] -= 1
                if remaining[child] == 0:
                    ready.append(child)
        if len(order) != len(nodes):
            raise ValueError('Graph is cyclic or not reachable from root.')
        return incoming, outgoing, order, tuple(sorted(hybrids))

    def parameters(self):
        hybrids = self.structure()[3]
        x = tuple(sp.Symbol(f'x{i}') for i in range(len(self.edges)))
        gamma = {v: sp.Symbol(f'g_{v}') for v in hybrids}
        return x, gamma


def compile_law(net: Network, mechanism: str = 'independent',
                forced: Mapping[str, int] | None = None,
                samples: Mapping[str, tuple[str, ...]] | None = None,
                edge_values: Mapping[int, object] | None = None,
                inheritance_values: Mapping[str, object] | None = None) -> dict:
    """Rooted gene-tree law, preserving the full joint frontier distribution.

    `forced[h]=0/1` picks the corresponding incoming edge in input edge order.
    Other hybrids use independent lineage choices or a common locus choice.
    Optional exact parameter substitutions are useful for larger replay cases.
    """
    if mechanism not in ('independent', 'common'):
        raise ValueError('Unknown inheritance mechanism.')
    inc, out, order, hybrids = net.structure()
    forced = dict(forced or {})
    if not set(forced) <= set(hybrids) or any(b not in (0, 1) for b in forced.values()):
        raise ValueError('Invalid original hybrid ID or forced parental bit.')
    samples = dict(samples) if samples is not None else {v: (v,) for v in net.leaves}
    if not set(samples) <= set(net.leaves):
        raise ValueError('Samples must be attached to declared leaf taxa.')
    labels = sum((list(xs) for xs in samples.values()), [])
    if not labels or len(set(labels)) != len(labels) or any(not isinstance(t, str) for t in labels):
        raise ValueError('Need globally unique nonempty string sample labels.')
    x, gs = net.parameters()
    if edge_values and not set(edge_values) <= set(range(len(x))):
        raise ValueError('Unknown edge index.')
    if inheritance_values and not set(inheritance_values) <= set(hybrids):
        raise ValueError('Unknown inheritance ID.')
    x = tuple(sp.sympify((edge_values or {}).get(i, v)) for i, v in enumerate(x))
    gs = {h: sp.sympify((inheritance_values or {}).get(h, g)) for h, g in gs.items()}
    states = {(): sp.S.One}
    result = defaultdict(lambda: sp.S.Zero)
    for v in reversed(order):
        nxt = defaultdict(lambda: sp.S.Zero)
        for key, probability in states.items():
            frontier = dict(key)
            live = list(samples.get(v, ()))
            for e in out[v]:
                live.extend(frontier.pop(e, ()))
            fs = forest(live)
            if v == net.root:
                if frontier:
                    raise AssertionError('Unconsumed frontier at ancestral root.')
                for tree, factor in root_kernel(fs):
                    result[tree] += probability * factor
                continue
            if len(inc[v]) == 1:
                routes = [((fs,), sp.S.One)]
            elif v in forced:
                routes = [(((fs, ()) if forced[v] == 0 else ((), fs)), sp.S.One)]
            elif mechanism == 'common':
                routes = [((fs, ()), gs[v]), (((), fs), 1 - gs[v])]
            else:
                routes = []
                for bits in product((0, 1), repeat=len(fs)):
                    left = forest(t for t, b in zip(fs, bits) if b == 0)
                    right = forest(t for t, b in zip(fs, bits) if b == 1)
                    routes.append(((left, right), gs[v]**len(left) * (1 - gs[v])**len(right)))
            for routed, route_prob in routes:
                kernels = [edge_kernel(group, x[e]) for group, e in zip(routed, inc[v])]
                for transitions in product(*kernels):
                    nf = dict(frontier)
                    factor = probability * route_prob
                    for e, (group, transition_prob) in zip(inc[v], transitions):
                        if group:
                            nf[e] = group
                        factor *= transition_prob
                    nxt[tuple(sorted(nf.items()))] += factor
        if v != net.root:
            states = {k: sp.expand(p) for k, p in nxt.items() if p != 0}
    return {t: sp.expand(p) for t, p in result.items() if p != 0}


def tipset(t: Tree) -> frozenset:
    return frozenset((t,)) if isinstance(t, str) else tipset(t[0]) | tipset(t[1])


def split_signature(t: Tree) -> tuple:
    """Canonical nontrivial split set of the unrooted, root-suppressed tree."""
    whole = tipset(t)
    splits = set()
    def visit(node):
        if isinstance(node, str):
            return
        side = tipset(node)
        other = whole - side
        if len(side) >= 2 and len(other) >= 2:
            splits.add(tuple(sorted((tuple(sorted(side)), tuple(sorted(other))))))
        visit(node[0]); visit(node[1])
    visit(t)
    return tuple(sorted(splits))


def unrooted_law(rooted: Mapping) -> dict:
    ans = defaultdict(lambda: sp.S.Zero)
    for t, p in rooted.items():
        ans[split_signature(t)] += p
    return {k: sp.expand(p) for k, p in ans.items()}


def evaluate(law: Mapping, substitutions: Mapping) -> dict:
    result = {t: sp.cancel(p.subs(substitutions)) for t, p in law.items()}
    if any(p.free_symbols for p in result.values()):
        raise ValueError('Not all law parameters were assigned.')
    return result
