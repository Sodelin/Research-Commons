"""Exact rational full-metric-genealogy density compiler and equality checker.

The returned exponential polynomial is symbolic, not a floating-point likelihood.
Scope: dated binary DAGs, constant positive pair-coalescence rates per population,
instantaneous independent or common inheritance, contemporaneous distinct leaves.
Classical coalescent-history calculation is prior work. See PROOFS.md for the
cellwise exponential-polynomial equality argument and its encoding restriction.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
from typing import Iterator
import math
import networkx as nx


def rational(x) -> F:
    if isinstance(x, (float, bool)):
        raise ValueError('Exact rational input required, not float/bool')
    return F(x)


@dataclass(frozen=True)
class Edge:
    id: str
    parent: str
    child: str
    rate: F
    inheritance: F | None = None


@dataclass
class Network:
    ages: dict[str, F]
    edges: tuple[Edge, ...]
    root_rate: F = F(1)

    def __post_init__(self):
        self.ages = {v: rational(a) for v, a in self.ages.items()}
        self.edges = tuple(Edge(e.id, e.parent, e.child, rational(e.rate),
                               None if e.inheritance is None else rational(e.inheritance))
                           for e in self.edges)
        self.root_rate = rational(self.root_rate)
        self.incoming = {v: [] for v in self.ages}
        self.outgoing = {v: [] for v in self.ages}
        if len({e.id for e in self.edges}) != len(self.edges) or '@stem' in {e.id for e in self.edges}:
            raise ValueError('Edge IDs must be unique; @stem is reserved')
        for e in self.edges:
            if e.parent not in self.ages or e.child not in self.ages:
                raise ValueError('Missing edge endpoint')
            self.incoming[e.child].append(e)
            self.outgoing[e.parent].append(e)
        roots = [v for v in self.ages if not self.incoming[v]]
        if len(roots) != 1:
            raise ValueError('Exactly one root is required')
        self.root = roots[0]
        self.leaves = tuple(sorted(v for v in self.ages if not self.outgoing[v]))
        self.rates = {e.id: e.rate for e in self.edges} | {'@stem': self.root_rate}
        self.validate()

    def validate(self, require_source: bool = False) -> dict:
        if self.root_rate <= 0 or not self.leaves:
            raise ValueError('Positive stem rate and nonempty leaves required')
        g = nx.DiGraph()
        g.add_nodes_from(self.ages)
        g.add_edges_from((e.parent, e.child) for e in self.edges)
        if not nx.is_directed_acyclic_graph(g):
            raise ValueError('Directed cycle')
        for v, age in self.ages.items():
            if age < 0:
                raise ValueError('Negative node age')
            deg = len(self.incoming[v]), len(self.outgoing[v])
            expected = (0, 2) if v == self.root else ((1, 0) if v in self.leaves else None)
            if expected is not None and deg != expected:
                raise ValueError(f'Invalid binary root/leaf degree: {v}: {deg}')
            if expected is None and deg not in ((1, 2), (2, 1)):
                raise ValueError(f'Invalid binary internal degree: {v}: {deg}')
            if v in self.leaves and age != 0:
                raise ValueError('This implementation requires contemporaneous leaves at zero')
            if len(self.incoming[v]) == 2:
                ps = [e.inheritance for e in self.incoming[v]]
                if any(p is None or not 0 < p < 1 for p in ps) or sum(ps) != 1:
                    raise ValueError('Interior complementary inheritance probabilities required')
            elif any(e.inheritance is not None for e in self.incoming[v]):
                raise ValueError('Inheritance labels belong only to hybrid incoming edges')
        for e in self.edges:
            if e.rate <= 0 or self.ages[e.parent] <= self.ages[e.child]:
                raise ValueError('Positive rates and strictly positive chronological edges required')
        # Root is LSA precisely when no other vertex dominates all sampled leaves.
        dom = {}
        for v in nx.topological_sort(g):
            preds = list(g.predecessors(v))
            dom[v] = {v} | (set.intersection(*(dom[p] for p in preds)) if preds else set())
        lsa_root = set.intersection(*(dom[v] for v in self.leaves)) == {self.root}
        ug = nx.Graph(g)
        multiplicity = Counter(frozenset((e.parent, e.child)) for e in self.edges)
        bridges = {frozenset(e) for e in nx.bridges(ug)}
        actual_bridges = {e.id for e in self.edges
                          if frozenset((e.parent, e.child)) in bridges
                          and multiplicity[frozenset((e.parent, e.child))] == 1}
        galled = all(self.outgoing[v][0].id in actual_bridges for v in self.ages
                     if len(self.incoming[v]) == 2)
        apex = object()
        aug = ug.copy()
        aug.add_edges_from((apex, v) for v in self.leaves)
        outer_labeled = nx.check_planarity(aug)[0]
        report = dict(binary=True, chronological=True, lsa_root=lsa_root,
                      galled_cut_child=galled, outer_labeled_planar=outer_labeled,
                      taxa=len(self.leaves), vertices=len(self.ages), edges=len(self.edges),
                      reticulations=sum(len(self.incoming[v]) == 2 for v in self.ages))
        if require_source and not (lsa_root and galled and outer_labeled and len(self.leaves) >= 4):
            raise ValueError(f'Outside the declared all-level source: {report}')
        return report

    def json(self):
        return {'ages': {v: str(a) for v, a in self.ages.items()},
                'edges': [{'id': e.id, 'parent': e.parent, 'child': e.child,
                           'rate': str(e.rate), 'inheritance': None if e.inheritance is None else str(e.inheritance)}
                          for e in self.edges], 'root_rate': str(self.root_rate)}

    @classmethod
    def from_json(cls, data):
        return cls(data['ages'], tuple(Edge(**e) for e in data['edges']), data.get('root_rate', '1'))


class BudgetExceeded(RuntimeError):
    pass


# Population states are ((live-clade bitmask, population edge id), ...).
# Polynomials map (intercept, t1 coefficient, ..., t_(n-1) coefficient) to F.

def _time_const(a: F, k: int):
    return (a,) + (F(0),) * k


def _time_var(j: int, k: int):
    return (F(0),) + tuple(F(i == j) for i in range(k))


def _accumulate(out, state, poly, factor=F(1)):
    if not factor:
        return
    dest = out.setdefault(state, {})
    for exp, a in poly.items():
        dest[exp] = dest.get(exp, F(0)) + factor * a
        if not dest[exp]:
            del dest[exp]


def _survive(states, prev, now, net):
    out = {}
    for state, poly in states.items():
        counts = Counter(edge for _, edge in state)
        rate = sum((F(k * (k - 1), 2) * net.rates[e] for e, k in counts.items()), F(0))
        shift = tuple(rate * (p - t) for p, t in zip(prev, now))
        out[state] = {tuple(x + y for x, y in zip(exp, shift)): a for exp, a in poly.items()}
    return out


def _node_event(states, node, net, mode):
    out = {}
    child_edges = {e.id for e in net.outgoing[node]}
    for state, poly in states.items():
        active = [clade for clade, edge in state if edge in child_edges]
        rest = [(clade, edge) for clade, edge in state if edge not in child_edges]
        parents = net.incoming[node]
        if not active:
            _accumulate(out, state, poly)
        elif not parents:
            dst = tuple(sorted(rest + [(c, '@stem') for c in active]))
            _accumulate(out, dst, poly)
        elif len(parents) == 1:
            dst = tuple(sorted(rest + [(c, parents[0].id) for c in active]))
            _accumulate(out, dst, poly)
        elif mode == 'com':
            for e in parents:
                dst = tuple(sorted(rest + [(c, e.id) for c in active]))
                _accumulate(out, dst, poly, e.inheritance)
        else:
            for choices in product(range(2), repeat=len(active)):
                weight = math.prod(parents[i].inheritance for i in choices)
                dst = tuple(sorted(rest + [(c, parents[i].id) for c, i in zip(active, choices)]))
                _accumulate(out, dst, poly, weight)
    return out


def _gene_event(states, pair, net):
    a, b = pair
    out = {}
    for state, poly in states.items():
        loc = dict(state)
        if a not in loc or b not in loc or loc[a] != loc[b]:
            continue
        edge = loc[a]
        dst = tuple(sorted([(c, e) for c, e in state if c not in (a, b)] + [(a | b, edge)]))
        _accumulate(out, dst, poly, net.rates[edge])
    return out


def validate_history(history, n):
    live = {1 << j for j in range(n)}
    if len(history) != n - 1:
        raise ValueError('A complete ranked binary history has n-1 merges')
    for a, b in history:
        if a == b or a not in live or b not in live or a & b:
            raise ValueError('Invalid merge history')
        live.difference_update((a, b))
        live.add(a | b)
    if live != {(1 << n) - 1}:
        raise ValueError('History does not end with all leaves')


def histories(n: int) -> Iterator[tuple]:
    if n < 2:
        raise ValueError('At least two samples required')
    def rec(live, prefix):
        if len(live) == 1:
            yield prefix
        else:
            for a, b in combinations(live, 2):
                nxt = tuple(sorted([c for c in live if c not in (a, b)] + [a | b]))
                yield from rec(nxt, prefix + ((a, b),))
    yield from rec(tuple(1 << j for j in range(n)), ())


def density(net: Network, history: tuple, bins: tuple[int, ...], mode='ind',
            boundaries=None, max_terms: int | None = 100000) -> dict:
    """Exact density on one open calendar cell. Gene event j is in interval bins[j]."""
    if mode not in ('ind', 'com'):
        raise ValueError('mode must be ind or com')
    if max_terms is not None and (type(max_terms) is not int or max_terms < 0):
        raise ValueError('max_terms must be a nonnegative integer or None')
    n, k = len(net.leaves), len(history)
    validate_history(history, n)
    own_bounds = {a for v, a in net.ages.items() if v not in net.leaves}
    bounds = tuple(sorted(own_bounds)) if boundaries is None else tuple(rational(x) for x in boundaries)
    if bounds != tuple(sorted(set(bounds))) or any(x <= 0 for x in bounds) or not own_bounds.issubset(bounds):
        raise ValueError('Boundaries must include every demographic node age')
    if len(bins) != k or tuple(sorted(bins)) != bins or any(type(b) is not int or b < 0 or b > len(bounds) for b in bins):
        raise ValueError('Invalid calendar cell')
    initial = tuple((1 << j, net.incoming[v][0].id) for j, v in enumerate(net.leaves))
    states = {initial: {_time_const(F(0), k): F(1)}}
    prev = _time_const(F(0), k)
    bi = 0
    for j, pair in enumerate(history):
        while bi < bins[j]:
            age = bounds[bi]
            now = _time_const(age, k)
            states = _survive(states, prev, now, net)
            for v in sorted(v for v, a in net.ages.items() if a == age and v not in net.leaves):
                states = _node_event(states, v, net, mode)
            prev = now
            bi += 1
            if max_terms is not None and sum(map(len, states.values())) > max_terms:
                raise BudgetExceeded('Density term limit')
        now = _time_var(j, k)
        states = _survive(states, prev, now, net)
        states = _gene_event(states, pair, net)
        prev = now
        if not states:
            return {}
        if max_terms is not None and sum(map(len, states.values())) > max_terms:
            raise BudgetExceeded('Density term limit')
    out = defaultdict(F)
    for poly in states.values():
        for exp, a in poly.items():
            out[exp] += a
    return {exp: a for exp, a in out.items() if a}


def difference(p, q):
    out = defaultdict(F)
    for e, a in p.items():
        out[e] += a
    for e, a in q.items():
        out[e] -= a
    return {e: a for e, a in out.items() if a}


def encode_poly(poly):
    return [{'exponent': list(map(str, e)), 'coefficient': str(a)}
            for e, a in sorted(poly.items())]


def equal_metric_laws(a: Network, b: Network, mode_a='ind', mode_b=None,
                      max_cells: int | None = 100000, max_terms=100000):
    """All histories and calendar cells are covered before 'equal' is returned.

    For rational data, nonempty canonical difference implies nonidentity by
    exponential-function independence and transcendence of exp(1). A finite limit
    returns UNKNOWN, never a truncated equality claim.
    """
    if a.leaves != b.leaves:
        raise ValueError('The sampled leaf labels must match')
    if mode_a not in ('ind', 'com') or (mode_b is not None and mode_b not in ('ind', 'com')):
        raise ValueError('Invalid inheritance mode')
    if max_cells is not None and (type(max_cells) is not int or max_cells < 0):
        raise ValueError('max_cells must be a nonnegative integer or None')
    bounds = tuple(sorted({v for net in (a, b) for node, v in net.ages.items() if node not in net.leaves}))
    count = 0
    try:
        for history in histories(len(a.leaves)):
            for bins in combinations_with_replacement(range(len(bounds) + 1), len(a.leaves) - 1):
                if max_cells is not None and count >= max_cells:
                    return {'status': 'unknown', 'cells_checked': count, 'reason': 'cell limit'}
                p = density(a, history, bins, mode_a, bounds, max_terms)
                q = density(b, history, bins, mode_a if mode_b is None else mode_b, bounds, max_terms)
                count += 1
                diff = difference(p, q)
                if diff:
                    return {'status': 'different', 'cells_checked': count,
                            'history': history, 'bins': bins, 'boundaries': list(map(str, bounds)),
                            'difference': encode_poly(diff)}
    except BudgetExceeded as exc:
        return {'status': 'unknown', 'cells_checked': count, 'reason': str(exc)}
    return {'status': 'equal', 'cells_checked': count}


def evaluate(poly, times):
    """Numerical illustration only; never used to decide equality."""
    return sum(float(a) * math.exp(float(e[0]) + sum(float(c) * t for c, t in zip(e[1:], times)))
               for e, a in poly.items())
