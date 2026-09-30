"""Exact, deterministic controls for ASTRA-STRUCTURAL-4S-20260930T1033Z.

Standard library only. Explicit rooted binary level-one networks, two actual
edge switchings, graph distances, and deduplicated quartet topologies.
Computational controls support, but do not replace, the parameter-uniform proof.
"""
from __future__ import annotations
from collections import deque
from fractions import Fraction as F
from itertools import combinations, permutations
from pathlib import Path
from hashlib import sha256
import json
import sys


class Network:
    def __init__(self):
        self.edges: set[tuple[str, str]] = set()
        self.leaves: dict[str, str] = {}
        self.root = 'root'
        self.hybrids: list[str] = []
        self.serial = 0

    def node(self, prefix='t'):
        self.serial += 1
        return f'{prefix}{self.serial}'

    def attach(self, parent, subtree):
        if isinstance(subtree, str):
            assert subtree not in self.leaves
            node = self.node('leaf')
            self.leaves[subtree] = node
            self.edges.add((parent, node))
        else:
            assert len(subtree) == 2
            node = self.node()
            self.edges.add((parent, node))
            self.attach(node, subtree[0]); self.attach(node, subtree[1])

    def validate(self):
        nodes = {v for e in self.edges for v in e}
        parents = {v: [] for v in nodes}; children = {v: [] for v in nodes}
        for u, v in self.edges: parents[v].append(u); children[u].append(v)
        assert set(self.leaves.values()) == {v for v in nodes if not children[v]}
        assert not parents[self.root] and len(children[self.root]) == 2
        for v in nodes - {self.root} - set(self.leaves.values()):
            assert (len(parents[v]), len(children[v])) == ((2, 1) if v in self.hybrids else (1, 2))
        for v in self.leaves.values(): assert len(parents[v]) == 1
        indeg = {v: len(parents[v]) for v in nodes}
        queue = deque([self.root]); seen = []
        while queue:
            v = queue.popleft(); seen.append(v)
            for w in children[v]:
                indeg[w] -= 1
                if indeg[w] == 0: queue.append(w)
        assert len(seen) == len(nodes), 'Directed cycle or disconnected source'
        # Every vertex's dominators are exactly the intersection over its parents.
        dom = {self.root: {self.root}}
        for v in seen[1:]:
            dom[v] = {v} | set.intersection(*(dom[p] for p in parents[v]))
        assert set.intersection(*(dom[v] for v in self.leaves.values())) == {self.root}, 'Root is not LSA'
        return {'vertices': len(nodes), 'arcs': len(self.edges), 'taxa': len(self.leaves),
                'binary': True, 'acyclic': True, 'root_is_LSA': True,
                'reticulations': len(self.hybrids)}

    def switching_distances(self):
        assert len(self.hybrids) == 1
        h = self.hybrids[0]; incoming = sorted(e for e in self.edges if e[1] == h)
        out = []
        for remove in incoming:
            adj = {}
            for u, v in self.edges - {remove}:
                adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
            assert sum(map(len, adj.values())) // 2 == len(adj) - 1
            distances = {}
            # Pruning and suppression are unnecessary for the four-point topology:
            # subdivision changes positive edge lengths, not induced topologies.
            for x, vx in self.leaves.items():
                dist = {vx: 0}; queue = deque([vx])
                while queue:
                    u = queue.popleft()
                    for v in adj[u]:
                        if v not in dist: dist[v] = dist[u] + 1; queue.append(v)
                assert len(dist) == len(adj)
                for y, vy in self.leaves.items(): distances[x, y] = dist[vy]
            out.append(distances)
        return out

    def quartets(self):
        switching = self.switching_distances(); result = {}
        for Q in combinations(sorted(self.leaves), 4):
            a, b, c, d = Q; topologies = set()
            for D in switching:
                sums = [D[a,b]+D[c,d], D[a,c]+D[b,d], D[a,d]+D[b,c]]
                low = min(sums)
                assert sums.count(low) == 1, (Q, sums)
                topologies.add(sums.index(low))
            assert 1 <= len(topologies) <= 2
            result[Q] = frozenset(topologies)
        return result


def comb(names):
    assert names
    return names[0] if len(names) == 1 else (names[0], comb(names[1:]))


def gall(order, hybrid, branches, root_edge):
    """One cycle, root inserted on an ordinary-ordinary cycle edge."""
    assert root_edge[0] != hybrid and root_edge[1] != hybrid
    n = Network(); cycle = {x: 'cycle_'+x for x in order}
    h = cycle[hybrid]; n.hybrids = [h]
    edge = {root_edge[0], root_edge[1]}
    adj = {x: set() for x in order}
    for i, u in enumerate(order):
        v = order[(i+1) % len(order)]
        if {u,v} == edge: continue
        adj[u].add(v); adj[v].add(u)
    assert len(adj[root_edge[0]]) == len(adj[root_edge[1]]) == 1
    for start in root_edge:
        n.edges.add((n.root, cycle[start])); previous = None; current = start
        while current != hybrid:
            choices = adj[current] - ({previous} if previous is not None else set())
            assert len(choices) == 1
            nxt = next(iter(choices)); n.edges.add((cycle[current], cycle[nxt]))
            previous, current = current, nxt
    for x in order: n.attach(cycle[x], branches.get(x, x))
    return n


def template(which, M=1):
    assert M >= 1
    P = comb(['p'] if M == 1 else [f'P{i}' for i in range(M)])
    Q = comb(['q'] if M == 1 else [f'Q{i}' for i in range(M)])
    if which == 'F1':
        net = gall(['x','p','y','q'], 'x',
                   {'p': ('z1', ('z2', ('z3', P))), 'q': Q}, ('p','y'))
        Y = ['x','y','z1','z2','z3']; chord = ('x','y')
    elif which == 'F2':
        net = gall(['p','u1','u2','u3','q','v1','v2'], 'p',
                   {'p': P, 'q': Q}, ('u1','u2'))
        Y = ['v1','v2','u1','u2','u3']; chord = ('v1','v2')
    elif which == 'F3':
        net = gall(['x','z1','p','y','q','z2'], 'x',
                   {'p': ('w',P), 'q': Q}, ('z1','p'))
        Y = ['x','w','y','z1','z2']; chord = ('x','w')
    else: raise ValueError(which)
    return net, Y, chord


def category(x,y,p,q,codes):
    Q = tuple(sorted((x,y,p,q))); assert len(set(Q)) == 4
    pairs = [(Q[0],Q[1]),(Q[0],Q[2]),(Q[0],Q[3])]
    tops = codes[Q]
    cherries = sum((x in pairs[t]) == (y in pairs[t]) for t in tops)
    if len(tops) == 1: return 0 if cherries else 1
    assert cherries in (0,1)
    return 2 if cherries else 3


def vec_counts(net, Y):
    codes = net.quartets(); n = len(net.leaves); out = {}
    for x,y in combinations(Y,2):
        counts = [0]*4
        for p,q in combinations(sorted(set(net.leaves)-{x,y}),2):
            counts[category(x,y,p,q,codes)] += 1
        out[x,y] = (2*n-4, *(2*t for t in counts))
    return out


def matrix_from_counts(counts, Y, scores):
    D = {(x,x):F(0) for x in Y}
    for (x,y),v in counts.items():
        D[x,y] = D[y,x] = F(v[0])+sum(F(a)*F(b) for a,b in zip(v[1:],scores))
    return D


def all_order_obstructions(D,Y):
    out=[]
    for tail in permutations(Y[1:]):
        if tail[0] > tail[-1]: continue
        C=(Y[0],)+tail; witness=None
        for i,j in combinations(range(len(C)),2):
            if j==i+1 or (i==0 and j==len(C)-1): continue
            a,b,c,d=C[i],C[(i+1)%len(C)],C[j],C[(j+1)%len(C)]
            alpha=D[a,c]+D[b,d]-D[a,d]-D[b,c]
            if alpha < 0: witness={'gaps':[i,j],'alpha':str(alpha)};break
        if witness is None: return None
        out.append({'order':list(C),**witness})
    assert len(out)==12
    return out


def padding_prediction(which,M):
    net,Y,chord=template(which); codes=net.quartets(); out={}; tables={}
    for x,y in combinations(Y,2):
        f=category(x,y,'p','q',codes); U=[0]*4; V=[0]*4
        others=[z for z in Y if z not in (x,y)]
        for z in others:
            for anchor in ('p','q'): U[category(x,y,anchor,z,codes)]+=1
        for u,v in combinations(others,2): V[category(x,y,u,v,codes)]+=1
        scores=[2*M*U[i]+2*V[i] for i in range(4)]
        scores[0]+=2*M*(M-1);scores[f]+=2*M*M
        out[x,y]=(4*M+6,*scores)
        tables[x+'|'+y]={'F_category':'csao'[f], 'U_counts':U,'V_counts':V}
    return out,tables


def controls():
    cases=[]; countchecks=0; equalitychecks=0
    expected={
      'F1': {'x|y':'o','x|z1':'s','x|z2':'s','x|z3':'s','y|z1':'s','y|z2':'s','y|z3':'s','z1|z2':'s','z1|z3':'s','z2|z3':'s'},
      'F2': {'v1|v2':'a','v1|u1':'o','v1|u2':'o','v1|u3':'o','v2|u1':'o','v2|u2':'o','v2|u3':'o','u1|u2':'a','u1|u3':'a','u2|u3':'a'},
      'F3': {'x|w':'s','x|y':'o','x|z1':'a','x|z2':'a','w|y':'s','w|z1':'s','w|z2':'s','y|z1':'s','y|z2':'s','z1|z2':'s'}
    }
    params={
      'F1': [(0,1,F(3,4),F(101,100)), (-7,-3,20,-2), (4,1,9,2)],
      'F2': [(0,1,2,1),(-5,-2,-1,-3),(7,19,F(1001,1000),1)],
      'F3': [(0,1,F(9,10),F(99,100)),(-8,-1,-2,-3),(9,2,1,0)]
    }
    for name in expected:
        net,Y,chord=template(name); admission=net.validate()
        pred,tables=padding_prediction(name,1)
        assert {k:v['F_category'] for k,v in tables.items()}==expected[name], (name,tables)
        for M in (1,2,3,5,8):
            large,Y,_=template(name,M);large.validate()
            actual=vec_counts(large,Y);pred,_=padding_prediction(name,M)
            assert actual==pred,(name,M,actual,pred)
            countchecks+=1;equalitychecks+=len(actual)*5
        witnesses=[]
        for scores in params[name]:
            c,s,a,o=map(F,scores); R=max(map(abs,(c,s,a,o)))
            delta={'F1':o-s,'F2':a-o,'F3':s-max(a,o)}[name]
            assert delta>0
            M=int(36*R/delta)+1
            counts,_=padding_prediction(name,M);D=matrix_from_counts(counts,Y,scores)
            cert=all_order_obstructions(D,Y);assert cert is not None
            u,v=chord;outsiders=[z for z in Y if z not in chord]
            gaps=[]
            for z,w in combinations(outsiders,2):
                target=D[u,v]+D[z,w]
                gaps.extend([target-D[u,z]-D[v,w], target-D[u,w]-D[v,z]])
            assert min(gaps)>0
            witnesses.append({'scores':[str(t) for t in scores], 'M':M,
                              'n':2*M+5,'minimum_chord_triangle_gap':str(min(gaps)),
                              'all_12_order_certificates':cert,
                              'execution':'Exact polynomial counts, not construction of padded graph at this M.'})
        cases.append({'family':name,'base_network':{'arcs':sorted(map(list,net.edges)),
                       'leaves':net.leaves,'root':net.root,'hybrids':net.hybrids},
                      'admission_checks':admission,'test_taxa':Y,'chord':chord,
                      'padding_tables':tables,'parameter_witnesses':witnesses})
    return {'status':'PASS_EXACT_FREE_O_CONTROLS',
            'method':'Explicit rooted graphs; actual edge switchings; BFS tree distances; topology sets deduplicated.',
            'source_admission_note':'Binary, acyclic and rooted-LSA properties checked. Single-cycle outer-labeled planarity and galledness follow the displayed construction; no general planarity recognizer used.',
            'direct_padded_graph_cases':countchecks,'exact_coefficient_equalities':equalitychecks,
            'all_order_parameter_witnesses':sum(len(c['parameter_witnesses']) for c in cases),
            'orders_per_witness':12,'families':cases,
            'limits':'Finite controls corroborate the separately written all-M counting and every-order proof. No Lean or external independent review.'}


if __name__=='__main__':
    report=controls();report['python']=sys.version
    report['checker_sha256']=sha256(Path(__file__).read_bytes()).hexdigest()
    dest=Path(__file__).with_name('FREE-O-EVIDENCE.json')
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='families'},indent=2))
