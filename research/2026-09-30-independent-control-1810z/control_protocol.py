"""Exact-rational quartet checks for a synchronized intervention compiler.

Author: Codex Work, INDEPENDENT-CONTROL-20260930-1810Z.
The first-merger recursion follows the audited algorithm in Astra's
cf_normal_form.py (ASTRA-BIO-PROVER-20260930-1612Z); this independent stdlib
implementation adds per-site mechanism choices and randomized row expansion.
It is a research prototype, not a biological actuator or a planarity validator.
The general full-gene-law result is a coupling proof, not inferred from tests.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass, replace
from fractions import Fraction as F
from itertools import combinations, product


@dataclass(frozen=True)
class Edge:
    parent: str
    child: str
    survival: F
    name: str


@dataclass
class Network:
    edges: tuple[Edge, ...]
    leaves: dict[str, str]
    inheritance: dict[str, F]  # probability of incoming edge 0

    def incoming(self, vertex):
        return tuple(e for e in self.edges if e.child == vertex)

    def outgoing(self, vertex):
        return tuple(e for e in self.edges if e.parent == vertex)

    def order(self):
        vertices = {v for e in self.edges for v in (e.parent, e.child)}
        done, result = set(), []
        while len(done) < len(vertices):
            ready = sorted(v for v in vertices - done
                           if all(e.parent in done for e in self.incoming(v)))
            if not ready:
                raise ValueError('directed cycle')
            result.extend(ready)
            done.update(ready)
        return tuple(result)

    def descendant_counts(self, sample_copies=None):
        """Count sampled copies reachable below each hybrid, not distinct paths.

        With one gene per taxon the default is 1 copy per labelled leaf.
        A proven source-graph admission is an external premise of the compiler.
        """
        copies = ({t: 1 for t in self.leaves.values()} if sample_copies is None
                  else dict(sample_copies))
        if set(copies) != set(self.leaves.values()) or any(
                type(x) is not int or x < 0 for x in copies.values()):
            raise ValueError('declare nonnegative integer copies for every taxon')
        reached = {}
        for v in reversed(self.order()):
            reached[v] = ({self.leaves[v]} if v in self.leaves else
                          set().union(*(reached[e.child] for e in self.outgoing(v))))
        return {h: sum(copies[t] for t in reached[h]) for h in self.inheritance}

    def structural_checks(self):
        """Degrees, LSA and cut children only; outer-label planarity is NOT checked."""
        order = self.order()
        if len({e.name for e in self.edges}) != len(self.edges):
            raise ValueError('duplicate edge IDs')
        roots = [v for v in order if not self.incoming(v)]
        if len(roots) != 1:
            raise ValueError('unique root required')
        root = roots[0]
        if len(set(self.leaves.values())) != len(self.leaves):
            raise ValueError('duplicate labels')
        if set(self.leaves) != {v for v in order if not self.outgoing(v)}:
            raise ValueError('labels must equal sinks')
        hybrids = set()
        for v in order:
            degree = len(self.incoming(v)), len(self.outgoing(v))
            if v == root:
                good = degree == (0, 2)
            elif v in self.leaves:
                good = degree == (1, 0)
            else:
                good = degree in ((1, 2), (2, 1))
                if degree == (2, 1):
                    hybrids.add(v)
            if not good:
                raise ValueError('nonbinary degrees')
        if hybrids != set(self.inheritance):
            raise ValueError('inheritance IDs must equal hybrids')
        dom = {}
        for v in order:
            parents = [e.parent for e in self.incoming(v)]
            dom[v] = {v} | (set.intersection(*(dom[p] for p in parents)) if parents else set())
        if set.intersection(*(dom[v] for v in self.leaves)) != {root}:
            raise ValueError('root is not LSA')
        def connected_without(edge):
            adj = defaultdict(set)
            for e in self.edges:
                if e.name != edge.name:
                    adj[e.parent].add(e.child)
                    adj[e.child].add(e.parent)
            seen, todo = {edge.parent}, [edge.parent]
            while todo:
                for w in adj[todo.pop()]:
                    if w not in seen:
                        seen.add(w); todo.append(w)
            return edge.child in seen
        if any(connected_without(self.outgoing(h)[0]) for h in hybrids):
            raise ValueError('hybrid child is not a cut edge')
        if any(type(e.survival) is not F or not 0 < e.survival < 1 for e in self.edges):
            raise ValueError('positive finite lengths required as rational survivals')
        if any(type(p) is not F or not 0 < p < 1 for p in self.inheritance.values()):
            raise ValueError('natural inheritance must be interior rational')
        return {'taxa': len(self.leaves), 'hybrids': len(hybrids), 'root': root,
                'vertices': len(order), 'edges': len(self.edges),
                'outer_labeled_planarity': 'external premise / fixture hand proof'}


def topology(pair):
    return {3: 0, 5: 1, 6: 2}[min(pair, 15 ^ pair)]


def cf(net, taxa, *, fixed=None, shared=()):
    """Exact quartet CF, naturally independent except specified shared sites.

    Fixed bit 0/1 selects the corresponding original incoming edge for every
    lineage. Multiple independent merges in disjoint populations yield the same
    quartet, so stopping at the first processed merger is valid for this marginal.
    """
    net.structural_checks()
    taxa = tuple(taxa)
    fixed, shared = dict(fixed or {}), set(shared)
    if len(taxa) != 4 or len(set(taxa)) != 4 or not set(taxa) <= set(net.leaves.values()):
        raise ValueError('four distinct sampled taxa required')
    if not (set(fixed) | shared) <= set(net.inheritance):
        raise ValueError('unknown control ID')
    if any(type(x) is not int or x not in (0, 1) for x in fixed.values()):
        raise ValueError('fixed controls must be bits')
    order = net.order(); ix = {v: i for i, v in enumerate(order)}
    roots = [v for v in order if not net.incoming(v)]
    if len(roots) != 1:
        raise ValueError('unique root required')
    root = roots[0]
    initial = [0] * len(order)
    for v, taxon in net.leaves.items():
        if taxon in taxa:
            initial[ix[v]] = 1 << taxa.index(taxon)
    states, answer = {tuple(initial): F(1)}, [F(0)] * 3

    def edge_pass(state, mass, edge, mask):
        bits = tuple(1 << j for j in range(4) if mask & (1 << j))
        rate = len(bits) * (len(bits)-1) // 2
        if rate:
            survive = edge.survival ** rate
            for a, b in combinations(bits, 2):
                answer[topology(a | b)] += mass * (1-survive) / rate
            mass *= survive
        s = list(state)
        if s[ix[edge.parent]] & mask:
            raise AssertionError('duplicated lineage')
        s[ix[edge.parent]] |= mask
        return tuple(s), mass

    for v in reversed(order):
        if v == root:
            continue
        ins = net.incoming(v); nxt = defaultdict(F)
        for state, mass in states.items():
            mask = state[ix[v]]
            clean = list(state); clean[ix[v]] = 0; clean = tuple(clean)
            if len(ins) == 1:
                s, weight = edge_pass(clean, mass, ins[0], mask)
                nxt[s] += weight
                continue
            if len(ins) != 2:
                raise ValueError('unsupported internal indegree')
            p = net.inheritance[v]
            if not mask:
                allocations = ((0, F(1)),)
            elif v in fixed:
                allocations = ((mask if fixed[v] == 0 else 0, F(1)),)
            elif v in shared:
                allocations = ((mask, p), (0, 1-p))
            else:
                allocations, sub = [], mask
                while True:
                    allocations.append((sub, p ** sub.bit_count() *
                                        (1-p) ** (mask ^ sub).bit_count()))
                    if sub == 0:
                        break
                    sub = (sub-1) & mask
            for sub, chance in allocations:
                s, weight = edge_pass(clean, mass * chance, ins[0], sub)
                s, weight = edge_pass(s, weight, ins[1], mask ^ sub)
                nxt[s] += weight
        states = {s: w for s, w in nxt.items() if w}
    for state, mass in states.items():
        if state[ix[root]] != 15 or sum(x.bit_count() for x in state) != 4:
            raise AssertionError('invalid final lineage state')
        for j in range(3):
            answer[j] += mass/3
    if sum(answer) != 1:
        raise AssertionError('lost probability mass')
    return tuple(answer)


@dataclass
class CompiledRow:
    network: Network
    fixed: dict[str, int]
    synchronize: tuple[str, ...]
    sample_copies: dict[str, int]

    def check_quartet(self, taxa):
        taxa = tuple(taxa)
        if any(self.sample_copies.get(t, 0) < 1 for t in taxa):
            raise ValueError('verifier quartet contains an undeclared sampled taxon')
        return taxa

    def sample_environment(self, rng):
        """Emit O(r) controls without enumerating exponentially many completions."""
        result = dict(self.fixed)
        for h in self.synchronize:
            p = self.network.inheritance[h]
            result[h] = 0 if rng.randrange(p.denominator) < p.numerator else 1
        return result

    def expanded_quartet_law(self, taxa, *, verification_site_cap=12):
        """Finite verification only; not used to sample the experimental protocol."""
        taxa = self.check_quartet(taxa)
        if type(verification_site_cap) is not int or verification_site_cap < 0:
            raise ValueError('verification site cap must be a nonnegative integer')
        if len(self.synchronize) > verification_site_cap:
            raise ValueError('verification expansion exceeds declared site cap')
        answer = [F(0)] * 3
        for bits in product((0, 1), repeat=len(self.synchronize)):
            force, chance = dict(self.fixed), F(1)
            for h, bit in zip(self.synchronize, bits):
                force[h] = bit
                p = self.network.inheritance[h]
                chance *= p if bit == 0 else 1-p
            law = cf(self.network, taxa, fixed=force)
            for j in range(3):
                answer[j] += chance * law[j]
        return tuple(answer)

    def sample_two_configuration_environment(self, rng):
        """Support-only compiler: one fresh coin for all additional controls.

        This emulates a correlated global-switch law, not the original product
        common-inheritance law. The partial-menu witness proof still applies.
        """
        result = dict(self.fixed)
        if self.synchronize:
            bit = rng.randrange(2)
            result.update({h: bit for h in self.synchronize})
        return result

    def two_configuration_quartet_law(self, taxa):
        taxa = self.check_quartet(taxa)
        answer = [F(0)] * 3
        for bit in (0, 1):
            force = dict(self.fixed)
            force.update({h: bit for h in self.synchronize})
            law = cf(self.network, taxa, fixed=force)
            for j in range(3):
                answer[j] += law[j]/2
        return tuple(answer)


def compile_row(net, row, *, graph_known=True, sample_copies=None):
    """Compile one nominal row on original IDs; no graph normalization.

    Supply every hybrid ID, using None for natural/free. Graph-free operation
    synchronizes every free hybrid. The graph-known reduction requires a valid
    descendant map; structural/planarity admission and ideal actuation remain
    scientific premises, rather than claims established by this function.
    """
    net.structural_checks()
    row = dict(row)
    if set(row) != set(net.inheritance):
        raise ValueError('declare a setting for every original hybrid ID')
    if any(x is not None and (type(x) is not int or x not in (0, 1)) for x in row.values()):
        raise ValueError('settings must be 0, 1, or None')
    copies = ({t:1 for t in net.leaves.values()} if sample_copies is None else dict(sample_copies))
    declared_counts = net.descendant_counts(copies)
    counts = declared_counts if graph_known else None
    fixed = {h: bit for h, bit in row.items() if bit is not None}
    sync = tuple(sorted(h for h in row if h not in fixed and
                        (counts is None or counts[h] >= 2)))
    return CompiledRow(net, fixed, sync, copies)


def sample_identifier_environment(row, probabilities, rng, *, two_configurations=False):
    """Graph-free runtime API: force every original ID using fixed or drawn bits.

    This requires an externally validated complete ID/parent map and actuator
    contract, but no network attachment graph. Costs count RNG calls/entries;
    arithmetic bit complexity also depends on the probability denominators.
    """
    row, probabilities = dict(row), dict(probabilities)
    if set(row) != set(probabilities):
        raise ValueError('row and probability IDs must agree')
    if any(x is not None and (type(x) is not int or x not in (0,1)) for x in row.values()):
        raise ValueError('settings must be 0, 1, or None')
    if any(type(p) is not F or not 0 < p < 1 for p in probabilities.values()):
        raise ValueError('interior rational parental probabilities required')
    free = tuple(h for h in row if row[h] is None)
    result = {h:b for h,b in row.items() if b is not None}
    if two_configurations:
        if free:
            bit = rng.randrange(2)
            result.update({h:bit for h in free})
    else:
        for h in free:
            p = probabilities[h]
            result[h] = 0 if rng.randrange(p.denominator) < p.numerator else 1
    return result


def triangle(*, bigons=0, extra_outgroup_taxa=0):
    """A triangle plus pendant bigons/tree, whose outer embedding is explicit."""
    raw = [('R','U',F(1,2)), ('U','V',F(1,10)), ('U','H',F(9,10)),
           ('V','C',F(1,2)), ('V','H',F(9,10)), ('H','W',F(9,10)),
           ('W','A',F(1,2)), ('W','B',F(1,2))]
    inheritance, leaves, previous = {'H':F(1,2)}, {'A':'A','B':'B','C':'C'}, 'R'
    for j in range(bigons):
        p, h = f'P{j}', f'J{j}'
        raw.extend(((previous,p,F(1,2)), (p,h,F(1,2)), (p,h,F(1,4))))
        inheritance[h] = F(1,2); previous = h
    if not extra_outgroup_taxa:
        raw.append((previous,'D',F(1,2))); leaves['D'] = 'D'
    else:
        raw.append((previous,'Z0',F(1,2)))
        for j in range(extra_outgroup_taxa):
            here = f'Z{j}'; label = chr(ord('D')+j)
            raw.append((here,label,F(1,2))); leaves[label] = label
            if j == extra_outgroup_taxa-1:
                last = chr(ord('D')+j+1)
                raw.append((here,last,F(1,2))); leaves[last] = last
            else:
                raw.append((here,f'Z{j+1}',F(1,2)))
    edges = tuple(Edge(a,b,x,f'e{k}') for k,(a,b,x) in enumerate(raw))
    return Network(edges, leaves, inheritance)


def triangle_formula(x0, u, v, w, gamma):
    a = 1-x0+x0*(gamma**2*(1-F(2,3)*u) +
                 (1-gamma)**2*(1-F(2,3)*v) + 2*gamma*(1-gamma)*w/3)
    return a, (1-a)/2, (1-a)/2


def indistinguishable_diamond():
    """Four-taxon controlled-profile competitor, with the same H,J0 IDs."""
    raw = [('R','P0',F(1,2)), ('P0','J0',F(1,2)), ('P0','J0',F(1,4)),
           ('J0','B',F(1,2)), ('R','U',F(1,2)), ('U','V',F(177,200)),
           ('U','W',F(177,200)), ('V','C',F(1,2)), ('V','H',F(1,2)),
           ('W','D',F(1,2)), ('W','H',F(1,2)), ('H','A',F(1,2))]
    edges = tuple(Edge(a,b,x,f'd{k}') for k,(a,b,x) in enumerate(raw))
    return Network(edges,{t:t for t in 'ABCD'},{'H':F(1,2),'J0':F(1,2)})


def contrast(law):
    return tuple(x-min(law) for x in law)
