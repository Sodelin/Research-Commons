"""Joint symbolic SOURCE compiler using the pinned G4 forest conventions.

All rows share one parameter/slot assignment. Original populations/parallel
edge IDs and live forest payloads remain joint. This is NOT a full core census.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import sys
import sympy as sp
import networkx as nx
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'upstream'))
from forest_algebra import forest,graft,edge_law,edge_polynomials
from source_checks import freeze

def compile_core(source,allocation,mode,forcing=None,edge_parameters=None,gamma_parameters=None,slots=None,protected_edges=()):
    source.validate();forcing=forcing or {};edge_parameters=edge_parameters or {};gamma_parameters=gamma_parameters or {};slots=slots or {}
    edges={e.name:e for e in source.edges}
    if mode not in ('common','independent'):raise ValueError('Unknown actual inheritance mechanism.')
    if set(edge_parameters)-set(edges) or set(gamma_parameters)-set(source.gamma):raise ValueError('Unknown original parameter identity.')
    if set(forcing)-set(source.gamma) or any(type(b) is not int or b not in (0,1) for b in forcing.values()):raise ValueError('Invalid original intervention.')
    if set(slots)-set(edges) or set(slots)&set(protected_edges):raise ValueError('Unknown or protected edge cannot become a fresh chain slot.')
    for name in slots:
        e=edges[name];graph=source.graph().to_undirected();graph.remove_edge(e.u,e.v,key=e.name)
        if nx.has_path(graph,e.u,e.v):raise ValueError('A source-word slot must be an actual bridge.')
    if set(allocation)!=set(source.taxa.values()) or any(type(n) is not int or n<1 for n in allocation.values()):raise ValueError('Every original taxon requires a fixed positive copy allocation.')
    labels={};count=0
    for taxon in sorted(allocation):labels[taxon]=tuple(range(count,count+allocation[taxon]));count+=allocation[taxon]
    incoming={v:sorted((e for e in source.edges if e.v==v),key=lambda e:e.name) for v in source.kinds}
    outgoing={v:[e for e in source.edges if e.u==v] for v in source.kinds}
    def edge(f,e):
        if e.name in slots:row=slots[e.name](len(f))
        else:
            x=edge_parameters.get(e.name,sp.Rational(e.x.numerator,e.x.denominator))
            row={g:sum(sp.Rational(c.numerator,c.denominator)*x**power for power,c in p.items()) for g,p in edge_polynomials(len(f)).items()}
        return [(graft(f,g),p) for g,p in row.items() if p!=0]
    states={():sp.S.One};result=defaultdict(lambda:sp.S.Zero)
    for v in reversed(list(nx.topological_sort(source.graph()))):
        kind=source.kinds[v];nxt=defaultdict(lambda:sp.S.Zero)
        for state,p in states.items():
            active=dict(state)
            f=tuple(labels[source.taxa[v]]) if kind=='leaf' else forest(t for e in outgoing[v] for t in active.pop(e.name))
            if kind=='root':
                for g,q in edge_law(len(f),Q(0)).items():
                    final=graft(f,g)
                    if len(final)!=1:raise ValueError('Actual ancestral root did not absorb.')
                    result[final[0]]+=p*sp.Rational(q.numerator,q.denominator)
                continue
            if kind=='hybrid':
                k=len(f);parents=incoming[v];gamma=gamma_parameters.get(v,sp.Rational(source.gamma[v].numerator,source.gamma[v].denominator))
                if v in forcing:routes=[((forcing[v],)*k,sp.S.One)]
                elif mode=='common':routes=[((0,)*k,gamma),((1,)*k,1-gamma)]
                else:routes=[(bits,gamma**bits.count(0)*(1-gamma)**bits.count(1)) for bits in product((0,1),repeat=k)]
                for bits,q in routes:
                    groups=[forest(t for i,t in enumerate(f) if bits[i]==a) for a in (0,1)]
                    for (f0,p0),(f1,p1) in product(edge(groups[0],parents[0]),edge(groups[1],parents[1])):
                        new=dict(active);new[parents[0].name]=f0;new[parents[1].name]=f1;nxt[freeze(new)]+=p*q*p0*p1
            else:
                for g,q in edge(f,incoming[v][0]):
                    new=dict(active);new[incoming[v][0].name]=g;nxt[freeze(new)]+=p*q
        if kind!='root':states=dict(nxt)
    result={t:sp.expand(p) for t,p in result.items() if p!=0}
    if sp.expand(sum(result.values())-1)!=0:raise ValueError('Joint symbolic source law failed normalization.')
    return result
