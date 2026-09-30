"""Exact quartet CFs, actual-source validation and a complete finite graph grammar.

Author: GPT-6 Astra Pro, ASTRA-BIO-PROVER-20260930-1612Z.
No simulation, floating point probability calculation, or full catalogue run.
Dependencies: Python 3, networkx; sympy only for symbolic/QF_NRA export.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
from typing import Any, Iterator
import networkx as nx


@dataclass(frozen=True)
class Edge:
    parent: str
    child: str
    survival: Any  # exp(-coalescent length)
    name: str


@dataclass
class Network:
    edges: list[Edge]
    leaves: dict[str, str]  # vertex -> taxon
    inheritance: dict[str, Any]  # probability of first incoming edge, edge-list order

    def dag(self):
        g = nx.DiGraph()
        g.add_edges_from((e.parent, e.child) for e in self.edges)
        return g

    def incoming(self, v):
        return [e for e in self.edges if e.child == v]

    def outgoing(self, v):
        return [e for e in self.edges if e.parent == v]

    def source_check(self, parameters: bool = True):
        """Check the declared binary/LSA/outer-labeled/galled multigraph contract."""
        g = self.dag()
        if not nx.is_directed_acyclic_graph(g):
            raise ValueError('not a DAG')
        if len({e.name for e in self.edges}) != len(self.edges):
            raise ValueError('edge IDs must be unique')
        roots = [v for v in g if not self.incoming(v)]
        if len(roots) != 1:
            raise ValueError('root is not unique')
        root = roots[0]
        if set(nx.descendants(g, root)) | {root} != set(g):
            raise ValueError('not all vertices reachable')
        if len(set(self.leaves.values())) != len(self.leaves):
            raise ValueError('duplicate taxon')
        if set(self.leaves) != {v for v in g if not self.outgoing(v)}:
            raise ValueError('leaf labels mismatch sinks')
        hybrids = set()
        for v in g:
            d = (len(self.incoming(v)), len(self.outgoing(v)))
            if v == root:
                if d != (0, 2): raise ValueError('root degrees')
            elif v in self.leaves:
                if d != (1, 0): raise ValueError('leaf degrees')
            elif d == (2, 1): hybrids.add(v)
            elif d != (1, 2): raise ValueError('nonbinary internal vertex')
        if hybrids != set(self.inheritance):
            raise ValueError('inheritance keys do not match hybrids')
        dom = {}
        for v in nx.topological_sort(g):
            ps = list(g.predecessors(v))
            dom[v] = {v} | (set.intersection(*(dom[p] for p in ps)) if ps else set())
        if set.intersection(*(dom[v] for v in self.leaves)) != {root}:
            raise ValueError('root is not the LSA of all taxa')
        u = nx.MultiGraph()
        for e in self.edges: u.add_edge(e.parent, e.child, key=e.name)
        bridges = set()
        for e in self.edges:
            u.remove_edge(e.parent, e.child, key=e.name)
            if not nx.has_path(u, e.parent, e.child): bridges.add(e.name)
            u.add_edge(e.parent, e.child, key=e.name)
        for h in hybrids:
            if self.outgoing(h)[0].name not in bridges:
                raise ValueError('hybrid child is not a cut edge')
        # All labelled leaves are cofacial iff adding a universal leaf-apex is planar.
        a = nx.Graph(u)
        apex = object()
        a.add_edges_from((apex, v) for v in self.leaves)
        if not nx.check_planarity(a)[0]:
            raise ValueError('not outer-labeled planar')
        if parameters:
            if not all(0 < e.survival < 1 for e in self.edges):
                raise ValueError('population lengths not finite and strictly positive')
            if not all(0 < h < 1 for h in self.inheritance.values()):
                raise ValueError('inheritance not interior')
        return {'vertices': len(g), 'edges': len(self.edges), 'taxa': len(self.leaves),
                'hybrids': len(hybrids), 'root': root, 'bridges': sorted(bridges)}

    def quartets(self):
        return combinations(sorted(self.leaves.values()), 4)


def pair_topology(mask: int) -> int:
    """Quartet order: 01|23, 02|13, 03|12 for four sorted sample labels."""
    canonical = min(mask, 15 ^ mask)
    return {3: 0, 5: 1, 6: 2}[canonical]


def cf(net: Network, taxa: tuple[str, str, str, str], mechanism='ind'):
    """Exact killed first-merger recursion; works with Fraction or SymPy values.

    Reverse-topological processing may pick any order among unrelated populations.
    Two coalescences in unrelated populations involve disjoint label pairs and
    imply the same unrooted quartet. Thus the first PROCESSED coalescence suffices.
    No-merger states carry four distinct singleton lineage bits.
    """
    if mechanism not in ('ind', 'com'):
        raise ValueError('mechanism must be ind or com')
    if len(taxa) != 4 or len(set(taxa)) != 4 or not set(taxa) <= set(net.leaves.values()):
        raise ValueError('need four distinct sampled taxa')
    order = list(nx.topological_sort(net.dag()))
    ix = {v: i for i, v in enumerate(order)}
    root = order[0]
    initial = [0] * len(order)
    for v, label in net.leaves.items():
        if label in taxa: initial[ix[v]] = 1 << taxa.index(label)
    states = {tuple(initial): F(1)}
    answer = [F(0), F(0), F(0)]

    def edge_pass(state, mass, edge, mask):
        k = mask.bit_count()
        rate = k * (k-1) // 2
        if rate:
            survive = edge.survival ** rate
            first_pair_mass = mass * (1 - survive) / rate
            bits = [1 << j for j in range(4) if mask & (1 << j)]
            for a, b in combinations(bits, 2):
                answer[pair_topology(a | b)] += first_pair_mass
            mass *= survive
        s = list(state)
        if s[ix[edge.parent]] & mask:
            raise AssertionError('lineage duplication')
        s[ix[edge.parent]] |= mask
        return tuple(s), mass

    for v in reversed(order):
        if v == root: continue
        next_states = defaultdict(lambda: F(0))
        ins = net.incoming(v)
        for state, mass in states.items():
            mask = state[ix[v]]
            clean = list(state); clean[ix[v]] = 0; clean = tuple(clean)
            if len(ins) == 1:
                s, w = edge_pass(clean, mass, ins[0], mask)
                next_states[s] += w
            elif len(ins) == 2:
                h = net.inheritance[v]
                if mask == 0:
                    allocations = [(0, F(1))]
                elif mechanism == 'com':
                    allocations = [(mask, h), (0, 1-h)]
                else:
                    allocations = []
                    sub = mask
                    while True:
                        allocations.append((sub, h ** sub.bit_count() *
                                            (1-h) ** ((mask ^ sub).bit_count())))
                        if sub == 0: break
                        sub = (sub - 1) & mask
                for sub, weight in allocations:
                    s, w = edge_pass(clean, mass * weight, ins[0], sub)
                    s, w = edge_pass(s, w, ins[1], mask ^ sub)
                    next_states[s] += w
            else:
                raise ValueError('unsupported indegree')
        states = dict(next_states)
    for state, mass in states.items():
        assert state[ix[root]] == 15 and sum(x.bit_count() for x in state) == 4
        for j in range(3): answer[j] += mass / 3
    return tuple(answer)


def switched_trees(net: Network):
    hs = sorted(net.inheritance)
    for choices in product((0, 1), repeat=len(hs)):
        keep = {h: net.incoming(h)[c].name for h, c in zip(hs, choices)}
        weight = F(1)
        for h, c in zip(hs, choices):
            p = net.inheritance[h]
            weight *= p if c == 0 else 1-p
        edges = [e for e in net.edges if e.child not in keep or keep[e.child] == e.name]
        yield edges, weight


def tree_splits(edges, leaves):
    """No pruning shortcut: compute taxon bipartition induced by each tree edge."""
    g = nx.Graph()
    g.add_edges_from((e.parent, e.child) for e in edges)
    total = frozenset(leaves.values())
    out = {}
    for e in edges:
        g.remove_edge(e.parent, e.child)
        vertices = nx.node_connected_component(g, e.parent)
        side = frozenset(leaves[v] for v in vertices if v in leaves)
        other = total - side
        key = tuple(sorted((tuple(sorted(side)), tuple(sorted(other)))))
        out[e.name] = (key, e.survival)
        g.add_edge(e.parent, e.child)
    return out


def support(net: Network):
    result = set()
    for edges, _ in switched_trees(net):
        for key, _x in tree_splits(edges, net.leaves).values():
            if min(map(len, key)) >= 2: result.add(key)
    return frozenset(result)


def common_cf_by_tree_mixture(net, taxa):
    """Independent check using displayed trees and quartet internal edge products."""
    ans = [F(0), F(0), F(0)]
    selected = {v: name for v, name in net.leaves.items() if name in taxa}
    for edges, weight in switched_trees(net):
        q = None; survival = F(1)
        for key, x in tree_splits(edges, selected).values():
            if len(key[0]) == len(key[1]) == 2:
                mask = sum(1 << taxa.index(a) for a in key[0])
                here = pair_topology(mask)
                if q is not None: assert q == here
                q = here; survival *= x
        assert q is not None
        for j in range(3):
            ans[j] += weight * (1-F(2,3)*survival if j == q else survival/3)
    return tuple(ans)


def complete_source_catalogue(n: int, max_reticulations=None) -> Iterator[Network]:
    """Finite, duplicate-permitting, COMPLETE combinatorial source grammar.

    Full normal-form bound is r <= 2n-3. No claim this is practical. All internal
    topological type orders and capacity-respecting upper-triangular multigraphs
    are visited. Leaves can always be placed last in a topological order.
    Parameters of returned graphs are placeholders, not a probability census.
    """
    if n < 2: raise ValueError('n must be at least two')
    bound = 2*n-3 if max_reticulations is None else max_reticulations
    if bound < 0: raise ValueError('negative cap')
    for r in range(bound+1):
        internal = n + 2*r - 2
        for hpos in combinations(range(1, internal+1), r):
            hs = set(hpos)
            N = 1 + internal + n
            indeg = [0] + [2 if v in hs else 1 for v in range(1, internal+1)] + [1]*n
            outdeg = [2] + [1 if v in hs else 2 for v in range(1, internal+1)] + [0]*n
            arcs = []
            remaining = indeg[:]
            def visit(v):
                if v == N:
                    if any(remaining): return
                    es = [Edge(str(a), str(b), F(1,2), f'e{i}') for i,(a,b) in enumerate(arcs)]
                    net = Network(es, {str(v): f't{v-internal-1}' for v in range(internal+1,N)},
                                  {str(h): F(1,2) for h in hs})
                    try: net.source_check()
                    except ValueError: return
                    yield net
                    return
                if remaining[v]: return
                candidates = [w for w in range(v+1,N) if remaining[w] > 0]
                for kids in combinations_with_replacement(candidates, outdeg[v]):
                    if any(kids.count(w) > remaining[w] for w in set(kids)): continue
                    for w in kids: remaining[w] -= 1; arcs.append((v,w))
                    yield from visit(v+1)
                    for w in reversed(kids): remaining[w] += 1; arcs.pop()
            yield from visit(0)


def symbolic_model(net):
    import sympy as sp
    xs = {e.name: sp.Symbol('x_'+e.name) for e in net.edges}
    hs = {h: sp.Symbol('h_'+h) for h in net.inheritance}
    sym = Network([Edge(e.parent,e.child,xs[e.name],e.name) for e in net.edges],net.leaves.copy(),hs)
    return sym, list(xs.values()) + list(hs.values())


def smt_expression(expr):
    import sympy as sp
    expr = sp.sympify(expr)
    if expr.is_Rational:
        if expr.q == 1: return str(expr.p) if expr.p >= 0 else f'(- {-expr.p})'
        return f'(/ {smt_expression(sp.Integer(expr.p))} {expr.q})'
    if expr.is_Symbol: return str(expr)
    if expr.is_Add: return '(+ '+' '.join(smt_expression(a) for a in expr.args)+')'
    if expr.is_Mul: return '(* '+' '.join(smt_expression(a) for a in expr.args)+')'
    if expr.is_Pow and expr.exp.is_Integer and expr.exp >= 0:
        if expr.exp == 0: return '1'
        return '(* '+' '.join([smt_expression(expr.base)]*int(expr.exp))+')'
    raise ValueError(f'not a polynomial: {expr}')


def model_image_smt(net, observations, mechanism='ind', boxes=False):
    """Export exact rational CF/image membership with strict positive parameters.

    observations maps sorted quartet tuples to length-three exact rational tuples,
    or to length-three pairs (lo,hi) when boxes=True. This is a single graph image,
    NOT a whole-class decision unless the complete catalogue is exhausted.
    """
    import sympy as sp
    sym, variables = symbolic_model(net)
    lines = ['(set-logic QF_NRA)']
    for x in variables:
        lines += [f'(declare-const {x} Real)', f'(assert (and (< 0 {x}) (< {x} 1)))']
    for q, obs in observations.items():
        if len(obs) != 3: raise ValueError('each quartet needs three coordinates')
        if tuple(sorted(q)) != tuple(q): raise ValueError('quartet labels must be sorted')
        probs = cf(sym, q, mechanism)
        for p, val in zip(probs, obs):
            formula = smt_expression(sp.expand(p))
            if boxes:
                lo,hi = val
                lines.append(f'(assert (and (<= {smt_expression(lo)} {formula}) (<= {formula} {smt_expression(hi)})))')
            else:
                lines.append(f'(assert (= {formula} {smt_expression(val)}))')
    lines.append('(check-sat)')
    return '\n'.join(lines)+'\n'


def normalize_two_port(net: Network, mechanism='ind'):
    """Construct a positive source representative, removing full two-port blobs.

    This routine is for exact rational survival/inheritance parameters. It is not
    an inference procedure and does not preserve original interventions or IDs.
    Root-core CF probes use formal zero-length attachments, never actual output
    edges. Every input, intermediate graph and output is source-checked.
    """
    if mechanism not in ('ind', 'com'):
        raise ValueError('mechanism must be ind or com')
    work = Network(net.edges[:], net.leaves.copy(), net.inheritance.copy())
    trace = []
    while True:
        info = work.source_check()
        bridges = set(info['bridges'])
        g = nx.Graph()
        g.add_edges_from((e.parent, e.child) for e in work.edges if e.name not in bridges)
        options = []
        for vertices in nx.connected_components(g):
            incident = [e for e in work.edges if (e.parent in vertices) != (e.child in vertices)]
            if len(incident) == 2:
                options.append((info['root'] in vertices, vertices, incident))
        if not options:
            work.source_check()
            return work, trace
        is_root, vertices, incident = min(options, key=lambda o: o[0])
        core = [e for e in work.edges if e.parent in vertices and e.child in vertices]
        serial = len(trace)
        prefix = f'NF{serial}_'
        existing = set(work.dag()) | {e.name for e in work.edges}
        while any(name.startswith(prefix) for name in existing):
            prefix += 'x'
        outside = [e for e in work.edges if e not in core and e not in incident]
        hs = {h:p for h,p in work.inheritance.items() if h not in vertices}
        if not is_root:
            upper = [e for e in incident if e.child in vertices]
            lower = [e for e in incident if e.parent in vertices]
            assert len(upper) == len(lower) == 1
            upper, lower = upper[0], lower[0]
            U, H = upper.child, lower.parent
            assert vertices == {U,H} and len(core) == 2
            assert all(e.parent == U and e.child == H for e in core)
            h = work.inheritance[H]
            x1, x2 = (e.survival for e in core)
            p = (h*h*x1+(1-h)**2*x2+2*h*(1-h) if mechanism == 'ind'
                 else h*x1+(1-h)*x2)
            assert 0 < p < 1
            outside.append(Edge(upper.parent, lower.child,
                                upper.survival*p*lower.survival, prefix+'effective'))
            trace.append({'kind':'nonroot', 'removed_core_edges':[e.name for e in core],
                          'consumed_incident_edges':[upper.name,lower.name],
                          'core_survival':str(p)})
        else:
            assert all(e.parent in vertices and e.child not in vertices for e in incident)
            probe_edges = core[:]
            probe_leaves = {}
            labels = []
            for i,e in enumerate(incident):
                z = prefix+f'Z{i}'
                probe_edges.append(Edge(e.parent,z,F(1),prefix+f'probe{i}'))
                for j in range(2):
                    leaf = prefix+f'gene{i}{j}'
                    labels.append(leaf);probe_leaves[leaf] = leaf
                    probe_edges.append(Edge(z,leaf,F(1),prefix+f'probe{i}{j}'))
            probe = Network(probe_edges,probe_leaves,
                            {h:p for h,p in work.inheritance.items() if h in vertices})
            a = cf(probe,tuple(labels),mechanism)[0]
            p = F(3,2)*(1-a)
            assert 0 < p < 1
            for i,e in enumerate(incident):
                outside.append(Edge(prefix+'ROOT',e.child,e.survival*(p if i else F(1)),
                                    prefix+f'rootedge{i}'))
            trace.append({'kind':'root', 'removed_core_edges':[e.name for e in core],
                          'consumed_incident_edges':[e.name for e in incident],
                          'correct_pair_cf':str(a),'core_survival':str(p)})
        work = Network(outside,work.leaves.copy(),hs)


def classify_global_cf(taxa, observations, solver, mechanism='ind', boxes=False,
                       max_reticulations=None, max_graphs=None):
    """Catalogue-and-image controller; the unrestricted catalogue can be enormous.

    solver(smt_string) must return 'sat', 'unsat' or an unknown/unavailable result.
    A restricted cap or an unfinished run NEVER yields an all-class certificate.
    max_graphs bounds yielded graphs, not raw generator steps or wall-clock time.
    Use an external execution budget for a strict practical runtime wrapper.
    """
    taxa = tuple(sorted(taxa))
    if len(taxa) < 4 or len(set(taxa)) != len(taxa):
        raise ValueError('need at least four distinct taxa')
    required = set(combinations(taxa,4))
    if set(observations) != required:
        raise ValueError('a COMPLETE correctly ordered quartet vector is required')
    for q,obs in observations.items():
        if len(obs) != 3: raise ValueError('each quartet requires three coordinates')
        for value in obs:
            if boxes:
                if len(value) != 2 or F(value[0]) > F(value[1]):
                    raise ValueError('invalid rational interval')
                F(value[0]); F(value[1])
            else: F(value)
    full_bound = 2*len(taxa)-3
    cap = full_bound if max_reticulations is None else max_reticulations
    if max_graphs is not None and max_graphs < 0: raise ValueError('negative graph budget')
    feasible = set(); unknown_targets = set(); tested = 0; exhausted = True
    for net in complete_source_catalogue(len(taxa), cap):
        if max_graphs is not None and tested >= max_graphs:
            exhausted = False
            break
        net.leaves = {v:taxa[int(label[1:])] for v,label in net.leaves.items()}
        target = support(net)
        # One feasible representative suffices; all alternatives still matter.
        if target in feasible:
            tested += 1
            continue
        verdict = solver(model_image_smt(net,observations,mechanism,boxes)).strip()
        tested += 1
        if verdict == 'sat':
            feasible.add(target); unknown_targets.discard(target)
        elif verdict != 'unsat':
            unknown_targets.add(target)
    unknown_targets -= feasible
    complete = exhausted and not unknown_targets
    full_scope = cap >= full_bound
    status = ('incomplete' if not complete else
              'infeasible' if not feasible else 'unique' if len(feasible)==1 else 'ambiguous')
    full_status = status if complete and full_scope else 'INCONCLUSIVE'
    # Feasible witnesses alone are a lower set; do not present it as an outer set.
    outer = (feasible if complete and full_scope else 'ALL_ADMITTED_TARGETS')
    return {'full_class_status':full_status,'enumerated_scope_status':status,
            'all_class_outer_candidates':outer,'solver_feasible_targets':feasible,
            'unknown_targets_in_visited_graphs':unknown_targets,'graphs_visited':tested,
            'catalogue_exhausted':exhausted,'reticulation_cap':cap,
            'full_normal_form_bound':full_bound}
