"""Source-critical G5 checks, not a source census or an independent review.

Exact arithmetic checks: selected-sample generator/pulse lumpability, frozen
population recovery by spectral projection, and chronological support pruning.
Only explicitly supplied admitted fixtures and finite algebra controls run.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import hashlib, json, math, platform
import networkx as nx
import sympy as sp


def partitions(items):
    items = tuple(items)
    if not items:
        yield ()
        return
    first, *tail = items
    for p in partitions(tail):
        yield tuple(sorted(((first,),) + p))
        for i, block in enumerate(p):
            yield tuple(sorted(p[:i] + (tuple(sorted((first,) + block)),) + p[i+1:]))


def restrict_state(state, chosen):
    return tuple(sorted((tuple(x for x in b if x in chosen), e)
                        for b, e in state if any(x in chosen for x in b)))


def generator(state, rates):
    out = defaultdict(F)
    for i, (a, e) in enumerate(state):
        for j in range(i + 1, len(state)):
            b, f = state[j]
            if e != f:
                continue
            merged = tuple(sorted(a + b))
            dst = tuple(sorted([v for k, v in enumerate(state) if k not in (i, j)] + [(merged, e)]))
            out[dst] += rates[e]
            out[state] -= rates[e]
    return {k: v for k, v in out.items() if v}


def pulse(state, g, mode):
    """All lineages in population zero encounter one binary hybrid."""
    active = [i for i, (_, e) in enumerate(state) if e == 0]
    if not active:
        return {state: F(1)}
    choices = [(j,) * len(active) for j in (0, 1)] if mode == 'common' else product((0, 1), repeat=len(active))
    out = defaultdict(F)
    for choices0 in choices:
        weight = (g if choices0[0] == 0 else 1-g) if mode == 'common' else F(1)
        dst = list(state)
        for i, j in zip(active, choices0):
            dst[i] = (state[i][0], j+2)
            if mode == 'independent':
                weight *= g if j == 0 else 1-g
        out[tuple(sorted(dst))] += weight
    return dict(out)


def project_law(law, chosen):
    out = defaultdict(F)
    for state, weight in law.items():
        out[restrict_state(state, chosen)] += weight
    return {k: v for k, v in out.items() if v}


def lumpability_checks():
    generator_count = pulse_count = 0
    rates = {0: F(2, 3), 1: F(7, 5)}
    for m in range(2, 6):
        items = tuple(range(m))
        chosen_sets = [set(c) for k in range(1, m) for c in combinations(items, k)]
        for p in partitions(items):
            for edges in product((0, 1), repeat=len(p)):
                state = tuple(zip(p, edges))
                for chosen in chosen_sets:
                    small = restrict_state(state, chosen)
                    assert project_law(generator(state, rates), chosen) == generator(small, rates)
                    generator_count += 1
                    for mode in ('common', 'independent'):
                        for g in (F(1, 5), F(1, 2)):
                            assert project_law(pulse(state, g, mode), chosen) == pulse(small, g, mode)
                            pulse_count += 1
    return {'generator_equalities': generator_count, 'hybrid_pulse_equalities': pulse_count,
            'max_algebra_sample_count': 5}


def matrix_for_population_partition(m, population, rates):
    states = list(partitions(range(m)))
    lookup = {p: i for i, p in enumerate(states)}
    owner = {x: i for i, b in enumerate(population) for x in b}
    valid = [p for p in states if all(len({owner[x] for x in b}) == 1 for b in p)]
    lookup = {p: i for i, p in enumerate(valid)}
    Q = sp.zeros(len(valid))
    for p, i in lookup.items():
        for u, a in enumerate(p):
            for v in range(u+1, len(p)):
                b = p[v]
                if owner[a[0]] != owner[b[0]]:
                    continue
                r = sp.Rational(rates[owner[a[0]]])
                dst = tuple(sorted(p[:u] + p[u+1:v] + p[v+1:] + (tuple(sorted(a+b)),)))
                Q[i, lookup[dst]] += r
                Q[i, i] -= r
    return valid, lookup, Q


def tomography_checks():
    rows = []
    for m in range(2, 5):
        for pop in partitions(range(m)):
            rates = [F(1) if i % 2 == 0 else F(3, 2) for i in range(len(pop))]
            states, lookup, Q = matrix_for_population_partition(m, pop, rates)
            frequencies = {F(0)}
            for block, r in zip(pop, rates):
                choices = [F(0)] + [F(j*(j-1), 2)*r for j in range(2, len(block)+1)]
                frequencies = {a+b for a in frequencies for b in choices}
            P = sp.eye(len(states))
            for beta in sorted(frequencies-{F(0)}):
                P = P*(sp.eye(len(states)) + Q/sp.Rational(beta))
            initial = lookup[tuple((i,) for i in range(m))]
            expected = sp.zeros(1, len(states)); expected[lookup[pop]] = 1
            assert P[initial, :] == expected
            assert (Q*P) == sp.zeros(len(states))
            rows.append({'m': m, 'population': pop, 'rates': list(map(str, rates)),
                         'frequencies': list(map(str, sorted(frequencies)))})
    # Equal rates still contain distinct hidden population partitions. A positive
    # mixture must be recovered as that mixture, not collapsed to one rate class.
    m = 4; allstates = list(partitions(range(m))); loc = {p:i for i,p in enumerate(allstates)}
    population_specs = [(((0, 1), (2, 3)), (F(1), F(1)), F(1, 1000000)),
                        (((0, 2), (1, 3)), (F(1), F(2)), F(2, 5)),
                        (((0, 1, 2, 3),), (F(1),), F(3, 5)-F(1, 1000000))]
    omega = {F(0)}; matrices=[]
    for pop, rates, w in population_specs:
        states, lookup, Q = matrix_for_population_partition(m, pop, rates)
        matrices.append((pop, states, lookup, Q, w))
        ff={F(0)}
        for block,r in zip(pop,rates):
            ff={a+b for a in ff for b in [F(0)]+[F(j*(j-1),2)*r for j in range(2,len(block)+1)]}
        omega |= ff
    projected=sp.zeros(1,len(allstates));truth=sp.zeros(1,len(allstates))
    mean_moments=[F(0)]*(2*20+1)
    for pop,states,lookup,Q,w in matrices:
        P=sp.eye(len(states))
        for beta in sorted(omega-{F(0)}):P=P*(sp.eye(len(states))+Q/sp.Rational(beta))
        start=lookup[tuple((i,) for i in range(m))]
        for p,i in lookup.items():projected[loc[p]] += sp.Rational(w)*P[start,i]
        truth[loc[pop]]+=sp.Rational(w)
        counts=sp.Matrix([len(p) for p in states]);power=sp.eye(len(states))
        for k in range(len(mean_moments)):
            mean_moments[k]+=F(w)*F((power*counts)[start])*(-1)**k
            power=power*Q
    assert projected==truth
    first_singular=None
    for d in range(1,20):
        H=sp.Matrix(d+1,d+1,lambda i,j:sp.Rational(mean_moments[i+j]))
        if H.det()==0:
            first_singular=d
            null=H.nullspace();assert len(null)==1
            z=sp.Symbol('z');p=sum(v*z**i for i,v in enumerate(null[0]))
            roots=sorted(sp.polys.polytools.ground_roots(p,z))
            break
        assert H.det()>0
    assert first_singular is not None
    expected_roots=[sp.Rational(0),sp.Rational(1),sp.Rational(2),sp.Rational(3),sp.Rational(6)]
    assert roots==expected_roots
    return {'single_assignment_projection_checks':len(rows),'mixture_projection_checks':1,
            'positive_spectrum_atoms':list(map(str,roots)), 'first_singular_hankel_order':first_singular,
            'controls':rows}


class Source:
    def __init__(self, record):
        self.name=record['name'];self.labels=tuple(record['labels'])
        self.ages={v:F(a) for v,a in record['ages'].items()}
        self.edges=tuple((e['id'],e['parent'],e['child']) for e in record['edges'])
        self.hybrids=set(record['inheritance'])
        self.ins={v:[] for v in self.ages};self.out={v:[] for v in self.ages}
        self.graph=nx.DiGraph();self.graph.add_nodes_from(self.ages)
        for eid,u,v in self.edges:
            self.ins[v].append(eid);self.out[u].append(eid);self.graph.add_edge(u,v)
        self.edge_map={e:(u,v) for e,u,v in self.edges}
        self.times=sorted(set(self.ages.values()))
        self.validate(record)
    def validate(self,record):
        assert nx.is_directed_acyclic_graph(self.graph)
        roots=[v for v in self.ages if not self.ins[v]];assert len(roots)==1
        self.root=roots[0]
        for v in self.ages:
            deg=(len(self.ins[v]),len(self.out[v]))
            assert deg==((0,2) if v==self.root else (1,0)) if v in self.labels or v==self.root else deg in ((1,2),(2,1))
        assert all(self.ages[u]>self.ages[v] for _,u,v in self.edges)
        assert all(self.ages[x]==0 for x in self.labels)
        assert all(F(e['rate'])>0 for e in record['edges']) and F(record['ancestral_rate'])>0
        assert all(0<F(g)<1 for g in record['inheritance'].values())
        U=nx.MultiGraph();U.add_nodes_from(self.ages)
        for eid,u,v in self.edges:U.add_edge(u,v,key=eid)
        for h in self.hybrids:
            eid=self.out[h][0];u,v=self.edge_map[eid];W=U.copy();W.remove_edge(u,v,eid)
            assert not nx.has_path(W,u,v)
        dom={}
        for v in nx.topological_sort(self.graph):
            parents=list(self.graph.predecessors(v))
            dom[v]={v}|(set.intersection(*(dom[p] for p in parents)) if parents else set())
        assert set.intersection(*(dom[x] for x in self.labels))=={self.root}
        aug=nx.Graph(U);aug.add_edges_from(('__apex__',x) for x in self.labels)
        assert nx.check_planarity(aug)[0]
    def table(self, chosen, mode):
        chosen=tuple(chosen)
        states={tuple(self.ins[x][0] for x in chosen)};answer={}
        for t in self.times:
            for v in sorted(v for v in self.ages if self.ages[v]==t and v not in self.labels):
                nextstates=set()
                for state in states:
                    ix=[i for i,e in enumerate(state) if e in self.out[v]]
                    parents=self.ins[v] or ['@stem']
                    choices=[(e,)*len(ix) for e in parents] if mode=='common' else product(parents,repeat=len(ix))
                    for cc in choices:
                        new=list(state)
                        for i,e in zip(ix,cc):new[i]=e
                        nextstates.add(tuple(new))
                states=nextstates
            parts=set()
            for state in states:
                groups=defaultdict(list)
                for x,e in zip(chosen,state):groups[e].append(x)
                parts.add(tuple(sorted(tuple(sorted(b)) for b in groups.values())))
            answer[t]=parts
        return answer
    def switching_clusters(self):
        result=set()
        for choice in product((0,1),repeat=len(self.hybrids)):
            hs=sorted(self.hybrids);keep={self.ins[h][v] for h,v in zip(hs,choice)}
            g=nx.DiGraph();g.add_nodes_from(self.ages)
            g.add_edges_from((u,v) for e,u,v in self.edges if v not in self.hybrids or e in keep)
            for v in g:
                B=({v}|nx.descendants(g,v)) & set(self.labels)
                if B:result.add(frozenset(B))
        return result


def route_checks(path):
    records=json.loads(Path(path).read_text());results=[];barriers=0;safe=0;lifts=0
    for rec in records:
        source=Source(rec);full_common=source.table(source.labels,'common')
        truth=source.switching_clusters()
        assert set(frozenset(b) for pp in full_common.values() for p in pp for b in p)==truth
        for mode in ('common','independent'):
            active={x:frozenset([x]) for x in source.labels};found=set(active.values())
            for t in source.times:
                while len(active)>1:
                    A=tuple(sorted(active));table=source.table(A,mode);parts=table[t]
                    # No already encountered hybrid can have >=2 retained descendants.
                    for h in source.hybrids:
                        D=set(nx.descendants(source.graph,h)) & set(A)
                        if source.ages[h]<=t:assert len(D)<2
                        if len(D)>=2:
                            _,c=source.edge_map[source.out[h][0]]
                            before=[z for z in source.times if source.ages[c]<=z<source.ages[h]]
                            assert before
                            for z in before:
                                assert all(tuple(sorted(D)) in p for p in table[z]);barriers+=1
                    common=source.table(A,'common')[t];assert parts==common;safe+=1
                    lifted={tuple(sorted(tuple(sorted(frozenset().union(*(active[x] for x in b)))) for b in p)) for p in parts}
                    assert lifted==full_common[t];lifts+=1
                    for p in parts:
                        for b in p:found.add(frozenset().union(*(active[x] for x in b)))
                    sure=set.intersection(*(set(p) for p in parts));large=sorted(b for b in sure if len(b)>1)
                    if not large:break
                    for b in large:
                        B=frozenset().union(*(active.pop(x) for x in b));active[min(b)]=B
                if len(active)==1:break
            assert len(active)==1 and found==truth
            naive=set(frozenset(b) for pp in source.table(source.labels,mode).values() for p in pp for b in p)
            results.append({'fixture':source.name,'mode':mode,'clusters_match':True,
                            'naive_false_clusters':len(naive-truth),'clusters':len(truth)})
    assert any(r['naive_false_clusters']>0 for r in results if r['mode']=='independent')
    return {'fixtures':len(records),'mode_comparisons':len(results),'child_bridge_checks':barriers,
            'safe_stage_equalities':safe,'complete_lift_equalities':lifts,'results':results}


def main():
    import argparse,time
    p=argparse.ArgumentParser();p.add_argument('fixtures');p.add_argument('output');args=p.parse_args()
    started=time.time()
    report={'evidence':'Exact finite self-audit; no independent review; not all-size proof',
            'python':platform.python_version(),'sympy':sp.__version__,'networkx':nx.__version__}
    report['lumpability']=lumpability_checks();print('lumpability',report['lumpability'],flush=True)
    report['tomography']=tomography_checks();print('tomography PASS',flush=True)
    report['routes']=route_checks(args.fixtures);print('routes', {k:v for k,v in report['routes'].items() if k!='results'},flush=True)
    report['status']='PASS';report['seconds']=round(time.time()-started,4)
    report['code_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['fixtures_sha256']=hashlib.sha256(Path(args.fixtures).read_bytes()).hexdigest()
    Path(args.output).write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
