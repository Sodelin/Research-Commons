"""Exact rational coalescent forest kernels and full rooted topology probabilities.

Coalescent-history / ancestral-configuration computation is prior work, including
Cummings et al. (2026), arXiv:2608.03544. This small independent implementation
checks interface identities; it is not a novelty claim for topology likelihoods.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
import math
import networkx as nx


def forest(trees):
    return tuple(sorted(trees, key=repr))


def merge(a, b):
    return forest((a, b))


def lam(k):
    return k * (k - 1) // 2


@lru_cache(None)
def death(k, j, x):
    """P(k lineages -> j) for pair survival x=exp(-t), by spectral formula."""
    if not (1 <= j <= k):
        raise ValueError('Invalid lineage counts')
    numerator = math.prod(lam(r) for r in range(j + 1, k + 1))
    return sum((F(numerator, math.prod(lam(m) - lam(l) for m in range(j, k + 1) if m != l))
                * x ** lam(l) for l in range(j, k + 1)), F(0))


@lru_cache(None)
def jump(f, j):
    if len(f) == j:
        return ((f, F(1)),)
    out = defaultdict(F)
    for i, k in combinations(range(len(f)), 2):
        nxt = forest([t for ix, t in enumerate(f) if ix not in (i, k)] + [merge(f[i], f[k])])
        for g, p in jump(nxt, j):
            out[g] += p / lam(len(f))
    return tuple(out.items())


@lru_cache(None)
def evolve(f, x):
    x = F(x)
    if not 0 <= x <= 1:
        raise ValueError('Pair survival must be in [0,1]')
    if not f:
        return (((), F(1)),)
    out = defaultdict(F)
    for j in range(1, len(f) + 1):
        pj = death(len(f), j, x)
        for g, weight in jump(f, j):
            out[g] += pj * weight
    return tuple((g, p) for g, p in out.items() if p)


def apply_edge(dist, x):
    out = defaultdict(F)
    for f, a in dist.items():
        for g, b in evolve(f, F(x)):
            out[g] += a * b
    return dict(out)


def apply_bigon(dist, x, y, gamma, mode='ind'):
    x, y, gamma = map(F, (x, y, gamma))
    if not (0 < x < 1 and 0 < y < 1 and 0 < gamma < 1):
        raise ValueError('Positive finite edges and interior inheritance required')
    if mode not in ('ind', 'com'):
        raise ValueError('Invalid inheritance mode')
    out = defaultdict(F)
    for f, a in dist.items():
        if mode == 'com':
            for z, weight in ((x, gamma), (y, 1 - gamma)):
                for g, b in evolve(f, z):
                    out[g] += a * weight * b
        else:
            for choices in product((0, 1), repeat=len(f)):
                f0 = forest(t for t, i in zip(f, choices) if i == 0)
                f1 = forest(t for t, i in zip(f, choices) if i == 1)
                weight = gamma ** len(f0) * (1 - gamma) ** len(f1)
                for g0, b0 in evolve(f0, x):
                    for g1, b1 in evolve(f1, y):
                        out[forest(g0 + g1)] += a * weight * b0 * b1
    return dict(out)


def pair_survival(x, y, gamma, mode):
    if mode not in ('ind', 'com'):
        raise ValueError('Invalid inheritance mode')
    x, y, g = map(F, (x, y, gamma))
    return (g * x + (1 - g) * y if mode == 'com' else
            g * g * x + (1 - g) ** 2 * y + 2 * g * (1 - g))


def common_moments(segments, n):
    """segments: ('edge',x) or ('bigon',x,y,gamma). Return m_j, 1<=j<=n."""
    result = {}
    for j in range(1, n + 1):
        m = F(1)
        for s in segments:
            if s[0] == 'edge':
                m *= F(s[1]) ** lam(j)
            elif s[0] == 'bigon':
                _, x, y, g = s
                x, y, g = map(F, (x, y, g))
                m *= g * x ** lam(j) + (1 - g) * y ** lam(j)
            else:
                raise ValueError('Unknown segment')
        result[j] = m
    return result


def from_common_moments(initial, moments):
    """Full topology-valued interface kernel from the n-1 spectral moments."""
    k = len(initial)
    out = defaultdict(F)
    for j in range(1, k + 1):
        num = math.prod(lam(r) for r in range(j + 1, k + 1))
        p = sum((F(num, math.prod(lam(m) - lam(l) for m in range(j, k + 1) if m != l))
                 * moments[l] for l in range(j, k + 1)), F(0))
        for g, w in jump(initial, j):
            out[g] += p * w
    return {g: p for g, p in out.items() if p}


def rooted_law(net, survivals, mode='ind', max_states=200000):
    """Full rooted, unranked gene topology law on a fixed supplied network.

    Survivals are independent exact rational x_e, not the metric module's
    rational rates. This is a different (coalescent-length) parameter encoding.
    The complete correlated population state is retained at hybrid splits.
    """
    if mode not in ('ind', 'com'):
        raise ValueError('Invalid inheritance mode')
    if set(survivals) != {e.id for e in net.edges}:
        raise ValueError('Supply every population-edge survival')
    x = {e: F(v) for e, v in survivals.items()}
    if any(not 0 < v < 1 for v in x.values()):
        raise ValueError('Positive finite populations require 0<x<1')
    graph = nx.DiGraph((e.parent, e.child) for e in net.edges)
    initial = tuple(sorted((v, (v,)) for v in net.leaves))
    states = {initial: F(1)}
    for node in reversed(list(nx.topological_sort(graph))):
        if node == net.root:
            break
        out = defaultdict(F)
        parents = net.incoming[node]
        for state, a in states.items():
            pending = dict(state)
            f = pending.pop(node, ())
            if len(parents) == 1:
                assignments = [((f,), F(1))]
            elif mode == 'com':
                assignments = [((f, ()), parents[0].inheritance),
                               (((), f), parents[1].inheritance)] if f else [(((), ()), F(1))]
            else:
                assignments = []
                for choices in product((0, 1), repeat=len(f)):
                    groups = tuple(forest(t for t, c in zip(f, choices) if c == i) for i in (0, 1))
                    p = math.prod(parents[i].inheritance ** len(groups[i]) for i in (0, 1))
                    assignments.append((groups, p))
            for groups, weight in assignments:
                edge_outputs = [evolve(group, x[e.id]) for group, e in zip(groups, parents)]
                for outputs in product(*edge_outputs):
                    nxt = dict(pending)
                    p = a * weight
                    for e, (g, b) in zip(parents, outputs):
                        nxt[e.parent] = forest(nxt.get(e.parent, ()) + g)
                        p *= b
                    nxt = tuple(sorted((v, ff) for v, ff in nxt.items() if ff))
                    out[nxt] += p
        states = dict(out)
        if max_states is not None and len(states) > max_states:
            raise RuntimeError('Incomplete: topology state limit reached')
    out = defaultdict(F)
    for state, a in states.items():
        pending = dict(state)
        if set(pending) != {net.root}:
            raise AssertionError('Not all lineages arrived at the root')
        for f, b in evolve(pending[net.root], F(0)):
            if len(f) != 1:
                raise AssertionError('Ancestral completion failed')
            out[f[0]] += a * b
    if sum(out.values()) != 1 or any(p < 0 for p in out.values()):
        raise AssertionError('Invalid probability law')
    return dict(out)


def tips(t):
    return frozenset((t,)) if isinstance(t, str) else tips(t[0]) | tips(t[1])


def unrooted_key(t):
    taxa = tips(t)
    splits = set()
    def visit(s):
        if isinstance(s, str):
            return
        a = tips(s)
        b = taxa - a
        if min(len(a), len(b)) >= 2:
            splits.add(min(tuple(sorted(a)), tuple(sorted(b))))
        visit(s[0]); visit(s[1])
    visit(t)
    return tuple(sorted(splits))


def unrooted_law(rooted):
    out = defaultdict(F)
    for t, p in rooted.items():
        out[unrooted_key(t)] += p
    return dict(out)


def restrict_tree(t, keep):
    if isinstance(t, str):
        return t if t in keep else None
    a, b = restrict_tree(t[0], keep), restrict_tree(t[1], keep)
    return b if a is None else a if b is None else merge(a, b)


def quartet_marginals(rooted):
    taxa = sorted(tips(next(iter(rooted))))
    out = {}
    for quartet in combinations(taxa, 4):
        law = defaultdict(F)
        for t, p in rooted.items():
            law[unrooted_key(restrict_tree(t, set(quartet)))] += p
        out[quartet] = dict(law)
    return out


def _null_vector(matrix):
    """One exact null vector; callers supply more columns than rows."""
    a = [list(map(F, row)) for row in matrix]
    rows, cols = len(a), len(a[0])
    pivots, r = [], 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        scale = a[r][c]
        a[r] = [v / scale for v in a[r]]
        for i in range(rows):
            if i != r and a[i][c]:
                scale = a[i][c]
                a[i] = [v - scale * w for v, w in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    free = next(c for c in range(cols) if c not in pivots)
    v = [F(0)] * cols
    v[free] = F(1)
    for i, c in enumerate(pivots):
        v[c] = -a[i][free]
    return v


def reduce_mixture(atoms, n):
    """Caratheodory reduction to <=n positive atoms at the n Kingman eigenrates.

    This is a generalized population-mixture kernel, NOT a claim of realization
    by a bounded binary source network. It preserves actual sampled moments.
    """
    if n < 1:
        raise ValueError('n must be positive')
    atoms = {F(x): F(w) for x, w in atoms.items() if w}
    if any(not 0 < x <= 1 or w < 0 for x, w in atoms.items()) or sum(atoms.values()) != 1:
        raise ValueError('A probability measure on positive survivals is required')
    while len(atoms) > n:
        xs = sorted(atoms)[:n + 1]
        v = _null_vector([[x ** lam(j) for x in xs] for j in range(1, n + 1)])
        positive = [i for i, a in enumerate(v) if a > 0]
        if not positive:
            raise AssertionError('The mass row must force both null-vector signs')
        step = min(atoms[xs[i]] / v[i] for i in positive)
        for x, a in zip(xs, v):
            atoms[x] -= step * a
            if not atoms[x]:
                del atoms[x]
            elif atoms[x] < 0:
                raise AssertionError('Negative quadrature weight')
    return atoms


def common_quadrature(segments, n):
    """Stream a chain: at most 2n atoms before reduction, <=n afterward."""
    atoms = {F(1): F(1)}
    peak = 1
    for s in segments:
        new = defaultdict(F)
        if s[0] == 'edge':
            choices = [(F(s[1]), F(1))]
        elif s[0] == 'bigon':
            _, x, y, g = s
            x, y, g = map(F, (x, y, g))
            if not (0 < x < 1 and 0 < y < 1 and 0 < g < 1):
                raise ValueError('Invalid bigon parameter')
            choices = [(x, g), (y, 1 - g)]
        else:
            raise ValueError('Unknown segment')
        for x, w in atoms.items():
            for y, p in choices:
                new[x * y] += w * p
        peak = max(peak, len(new))
        atoms = reduce_mixture(new, n)
    return atoms, peak
