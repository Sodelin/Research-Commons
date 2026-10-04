"""Exact source-level controls for the G4 finite-cap tester theorem.

This is a finite rooted-source compiler, not an exhaustive census of every
bounded core and not a source-realizability solver.  It retains the JOINT
population state.  Labels, parallel-edge IDs, and original hybrid IDs survive.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass,replace
from fractions import Fraction as Q
from itertools import product,combinations_with_replacement,combinations
from typing import Callable,Any,Iterator
import networkx as nx
from forest_algebra import (Tree,Forest,forest,tree,graft,leaves,relabel,edge_law,
    ForestAlgebra,bigon_law)

@dataclass(frozen=True)
class Edge:
    name:str
    u:str
    v:str
    x:Q

@dataclass
class Source:
    kinds:dict[str,str]
    taxa:dict[str,str]
    edges:tuple[Edge,...]
    gamma:dict[str,Q]
    def graph(self)->nx.MultiDiGraph:
        g=nx.MultiDiGraph()
        g.add_nodes_from(self.kinds)
        for e in self.edges:g.add_edge(e.u,e.v,key=e.name)
        return g
    def validate(self)->dict[str,Any]:
        g=self.graph()
        if len({e.name for e in self.edges})!=len(self.edges):
            raise ValueError('Original edge IDs must be unique.')
        if not nx.is_directed_acyclic_graph(g):raise ValueError('Not a DAG.')
        roots=[v for v,k in self.kinds.items() if k=='root']
        if len(roots)!=1:raise ValueError('Expected one root.')
        for v,k in self.kinds.items():
            expected={'root':(0,2),'tree':(1,2),'hybrid':(2,1),'leaf':(1,0)}[k]
            if (g.in_degree(v),g.out_degree(v))!=expected:
                raise ValueError(('Nonbinary source vertex',v))
        if any(not 0<e.x<1 for e in self.edges):
            raise ValueError('Every finite natural population edge must be strictly positive and finite.')
        hs={v for v,k in self.kinds.items() if k=='hybrid'}
        if set(self.gamma)!=hs or any(not 0<p<1 for p in self.gamma.values()):
            raise ValueError('Natural hybrid weights must be interior with exact original IDs.')
        if set(self.taxa)!={v for v,k in self.kinds.items() if k=='leaf'}:
            raise ValueError('Leaf-label map mismatch.')
        if len(set(self.taxa.values()))!=len(self.taxa):raise ValueError('Repeated taxon label.')
        if len(self.taxa)<4:raise ValueError('The registered source class requires at least four taxa.')
        ug=g.to_undirected()
        for h in hs:
            e=next(e for e in self.edges if e.u==h)
            q=ug.copy();q.remove_edge(e.u,e.v,key=e.name)
            if nx.has_path(q,e.u,e.v):
                raise ValueError(('Hybrid-child edge is not a cut edge',h))
        root=roots[0]
        dom=nx.immediate_dominators(nx.DiGraph(g),root)
        common=set(self.kinds)
        for v in self.taxa:
            ds={v}
            while v!=root:v=dom[v];ds.add(v)
            common &= ds
        if common!={root}:raise ValueError('The designated root is not the LSA of all taxa.')
        # Subdivide parallel arcs to use a simple planar-graph routine.  A new
        # apex adjacent to all labelled leaves tests whether those leaves can
        # lie on one face; the root itself need not lie on the outer face.
        sg=nx.Graph();sg.add_nodes_from(('v',v) for v in self.kinds)
        for e in self.edges:
            sg.add_edge(('v',e.u),('e',e.name));sg.add_edge(('e',e.name),('v',e.v))
        for v in self.taxa:sg.add_edge(('apex','*'),('v',v))
        planar,_=nx.check_planarity(sg)
        if not planar:raise ValueError('No common-face embedding for all taxon leaves.')
        return {'taxa':len(self.taxa),'reticulations':len(hs),'vertices':len(self.kinds),'edges':len(self.edges),
                'binary':True,'cut_child':True,'lsa_root':True,'outer_labelled_planar':True,'strict_positive_parameters':True}

def balanced()->Source:
    k={'R':'root','A':'tree','B':'tree',**{x:'leaf' for x in 'abcd'}}
    es=[('ra','R','A'),('rb','R','B'),('a','A','a'),('b','A','b'),('c','B','c'),('d','B','d')]
    return Source(k,{x:x for x in 'abcd'},tuple(Edge(n,u,v,Q(1,2)) for n,u,v in es),{})

def caterpillar()->Source:
    k={'R':'root','A':'tree','B':'tree',**{x:'leaf' for x in 'abcd'}}
    es=[Edge('rd','R','d',Q(1,2)),Edge('rb','R','B',Q(1,2)),Edge('ba','B','A',Q(1,4)),
        Edge('bc','B','c',Q(1,2)),Edge('aa','A','a',Q(1,2)),Edge('ab','A','b',Q(1,2))]
    return Source(k,{x:x for x in 'abcd'},tuple(es),{})

def root_two_hybrids()->Source:
    k={'R':'root','U':'tree','V':'tree','H0':'hybrid','H1':'hybrid','A':'tree','B':'tree',
       **{x:'leaf' for x in 'abcd'}}
    arcs=[('ru','R','U'),('rv','R','V'),('u0','U','H0'),('u1','U','H1'),
          ('v0','V','H0'),('v1','V','H1'),('h0a','H0','A'),('h1b','H1','B'),
          ('a','A','a'),('b','A','b'),('c','B','c'),('d','B','d')]
    return Source(k,{x:x for x in 'abcd'},tuple(Edge(n,u,v,Q((i%3)+1,(i%3)+3)) for i,(n,u,v) in enumerate(arcs)),
                  {'H0':Q(2,5),'H1':Q(3,7)})

def insert_chain(s:Source,edge_id:str,lead:Q,cells:tuple[tuple[Q,Q,Q,Q],...])->Source:
    """Insert only on an eligible bridge; keep a positive lead and connectors."""
    e=next(e for e in s.edges if e.name==edge_id)
    ug=s.graph().to_undirected();ug.remove_edge(e.u,e.v,key=e.name)
    if nx.has_path(ug,e.u,e.v):raise ValueError('A serial cut-child bigon may only replace a bridge.')
    k=dict(s.kinds);gs=dict(s.gamma);es=[q for q in s.edges if q.name!=edge_id]
    if not cells:
        es.append(Edge(edge_id,e.u,e.v,lead))
    else:
        lower=e.v
        for j,(x,y,g,a) in enumerate(cells,1):
            u=f'{edge_id}.U{j}';h=f'{edge_id}.H{j}'
            k[u]='tree';k[h]='hybrid';gs[h]=g
            low_x=lead if j==1 else cells[j-2][3]
            es.extend((Edge(f'{edge_id}.lower{j}',h,lower,low_x),Edge(f'{edge_id}.arm{j}.0',u,h,x),
                       Edge(f'{edge_id}.arm{j}.1',u,h,y)))
            lower=u
        es.append(Edge(f'{edge_id}.upper',e.u,lower,cells[-1][3]))
    out=Source(k,dict(s.taxa),tuple(es),gs);out.validate();return out

def freeze(d:dict[str,Forest])->tuple[tuple[str,Forest],...]:
    return tuple(sorted(d.items()))

def compile_source(s:Source,allocation:dict[str,int],mode:str,
                   forcing:dict[str,int]|None=None,
                   custom:dict[str,Callable[[int],dict[Forest,Q]]]|None=None)->dict[Tree,Q]:
    s.validate()
    if mode not in ('common','independent'):raise ValueError(mode)
    forcing=forcing or {};custom=custom or {}
    if any(h not in s.gamma or bit not in (0,1) for h,bit in forcing.items()):
        raise ValueError('Unknown original actuator ID or invalid fixed bit.')
    if set(allocation)!=set(s.taxa.values()) or any(k<1 for k in allocation.values()):
        raise ValueError('Declare at least one sampled copy for every taxon.')
    labels={};next_label=0
    for taxon in sorted(allocation):
        labels[taxon]=tuple(range(next_label,next_label+allocation[taxon]));next_label+=allocation[taxon]
    states={():Q(1)}
    result=defaultdict(Q)
    incoming={v:sorted((e for e in s.edges if e.v==v),key=lambda e:e.name) for v in s.kinds}
    outgoing={v:[e for e in s.edges if e.u==v] for v in s.kinds}
    def advance(f:Forest,e:Edge):
        row=custom[e.name](len(f)) if e.name in custom else edge_law(len(f),e.x)
        return [(graft(f,g),p) for g,p in row.items() if p]
    for v in reversed(list(nx.topological_sort(s.graph()))):
        kind=s.kinds[v];ns=defaultdict(Q)
        for state,p in states.items():
            d=dict(state)
            if kind=='leaf':f=tuple(labels[s.taxa[v]])
            else:f=forest(t for e in outgoing[v] for t in d.pop(e.name))
            if kind=='root':
                for g,q in edge_law(len(f),Q(0)).items():
                    t=graft(f,g)
                    if len(t)!=1:raise AssertionError('Ancestral absorption did not complete.')
                    result[t[0]]+=p*q
                continue
            if kind=='hybrid':
                parents=incoming[v];k=len(f)
                routes=[]
                if v in forcing:
                    bits=(forcing[v],)*k;routes=[(bits,Q(1))]
                elif mode=='common':
                    routes=[((0,)*k,s.gamma[v]),((1,)*k,1-s.gamma[v])]
                else:
                    g=s.gamma[v]
                    routes=[(bits,g**bits.count(0)*(1-g)**bits.count(1)) for bits in product((0,1),repeat=k)]
                for bits,q in routes:
                    ff=[forest(t for i,t in enumerate(f) if bits[i]==a) for a in (0,1)]
                    for (f0,p0),(f1,p1) in product(advance(ff[0],parents[0]),advance(ff[1],parents[1])):
                        z=dict(d);z[parents[0].name]=f0;z[parents[1].name]=f1
                        ns[freeze(z)]+=p*q*p0*p1
            else:
                e=incoming[v][0]
                for g,q in advance(f,e):
                    z=dict(d);z[e.name]=g;ns[freeze(z)]+=p*q
        if kind!='root':states=dict(ns)
    if sum(result.values(),Q(0))!=1 or any(p<0 for p in result.values()):
        raise ArithmeticError('The joint source law is not a probability vector.')
    return dict(result)

def quartet(t:Tree)->tuple[tuple[int,...],tuple[int,...]]:
    ll=set(leaves(t));found=[]
    def visit(x):
        if isinstance(x,int):return
        a=set(leaves(x))
        if len(a)==2:found.append(tuple(sorted((tuple(sorted(a)),tuple(sorted(ll-a))))))
        visit(x[0]);visit(x[1])
    visit(t)
    if not found or len(set(found))!=1:raise ValueError('Expected a four-leaf binary genealogy.')
    return found[0]


def project_quartets(law:dict[Tree,Q])->dict[Any,Q]:
    out=defaultdict(Q)
    for t,p in law.items():out[quartet(t)]+=p
    return dict(out)

def run()->dict[str,Any]:
    a4={x:1 for x in 'abcd'};a5={**a4,'a':2}
    cases=[]
    for base,slot in ((balanced(),'ra'),(root_two_hybrids(),'h0a')):
        cells=((Q(1,3),Q(3,5),Q(2,7),Q(4,5)),(Q(2,5),Q(5,7),Q(3,8),Q(3,4)))
        lead=Q(2,3);expanded=insert_chain(base,slot,lead,cells)
        for allocation in (a4,a5):
            m=sum(allocation.values());alg=ForestAlgebra(m)
            for mode in ('common','independent'):
                z=alg.edge(lead)
                for x,y,g,a in cells:z=alg.mul(z,alg.cell(x,y,g,a,mode))
                def kernel(k,z=z,alg=alg):
                    return {f:z[i] for i,(kk,f) in enumerate(alg.coords) if kk==k and z[i]}
                raw=compile_source(expanded,allocation,mode)
                reduced=compile_source(base,allocation,mode,custom={slot:kernel})
                if raw!=reduced:raise AssertionError('Raw source / forest-core mismatch.')
                cases.append({'base':'root-two-hybrids' if base.gamma else 'tree','cap':m,'mode':mode,
                              'gene_topologies':len(raw),'expanded_source':expanded.validate(),'exact_equality':True})
    # Actual positive four-taxon laws: rooted differences are not licensed when
    # the declared observation is only the unrooted quartet.
    p=compile_source(balanced(),a4,'common');q=compile_source(caterpillar(),a4,'common')
    if p==q or project_quartets(p)!=project_quartets(q):
        raise AssertionError('The projection negative control failed.')
    projection={'rooted_laws_differ':True,'authorized_quartet_laws_equal':True,
                'quartet_probabilities':{str(t):str(w) for t,w in project_quartets(p).items()}}
    # Original-ID forcing is applied once for the whole locus, not once per copy.
    s=root_two_hybrids();menu={}
    for mode in ('common','independent'):
        nat=compile_source(s,a5,mode)
        p0=compile_source(s,a5,mode,{'H0':0});p1=compile_source(s,a5,mode,{'H0':1})
        mix={t:s.gamma['H0']*p0.get(t,Q(0))+(1-s.gamma['H0'])*p1.get(t,Q(0)) for t in set(p0)|set(p1)}
        equal=nat==mix
        if equal!=(mode=='common'):raise AssertionError('Common coin / independent rerouting conflated.')
        menu[mode]={'natural_equals_same_gamma_endpoint_mixture':equal,'gene_topologies':len(nat)}
    rejected=False
    try:insert_chain(s,'ru',Q(1,2),((Q(1,2),Q(2,3),Q(1,2),Q(1,2)),))
    except ValueError:rejected=True
    if not rejected:raise AssertionError('Illegal nonbridge insertion was accepted.')
    return {'raw_vs_decorated_cases':cases,'projection_guard':projection,'whole_locus_control_guard':menu,
            'illegal_nonbridge_insertion_rejected':rejected,
            'scope':'Exact finite controls; no exhaustive bounded-core census or independent review.'}

if __name__=='__main__':
    import json,argparse
    p=argparse.ArgumentParser();p.add_argument('--output');args=p.parse_args()
    r=run();text=json.dumps(r,indent=2)
    if args.output:
        with open(args.output,'w') as f:f.write(text+'\n')
    print(text)
