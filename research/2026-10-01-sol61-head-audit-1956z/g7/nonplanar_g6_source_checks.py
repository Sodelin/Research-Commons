"""Focused actual-source controls for removing G6's embedding restriction.

Finite graph/target/cut guards only. No full image net or statistical engine.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import json,hashlib,platform
import networkx as nx
import nonplanar_calendar_q_checks as old

def insert_chain(cherry,L):
    edges,taxa,ages=old.source(cherry);old.audit(edges,taxa,ages)
    G=nx.MultiDiGraph();G.add_edges_from(edges)
    child='W' if cherry else 'a';G.remove_edge('H1',child)
    hi,lo=F(ages['H1']),F(ages[child]);step=(hi-lo)/(2*L+1)
    previous='H1';cells=[]
    for i in range(L):
        u,h=f'U{i}',f'J{i}';G.add_edge(previous,u)
        G.add_edge(u,h);G.add_edge(u,h);cells.append((u,h))
        ages[u]=hi-(2*i+1)*step;ages[h]=hi-(2*i+2)*step;previous=h
    G.add_edge(previous,child)
    return G,tuple(taxa),{k:F(v) for k,v in ages.items()},cells,hi,lo

def source_audit(G,taxa,ages):
    assert nx.is_directed_acyclic_graph(G) and set(nx.descendants(G,'R'))|{'R'}==set(G)
    hybrids=[]
    for v in G:
        d=(G.in_degree(v),G.out_degree(v))
        if v=='R':assert d==(0,2)
        elif v in taxa:assert d==(1,0)
        elif d==(2,1):hybrids.append(v)
        else:assert d==(1,2)
    assert all(ages[u]>ages[v] for u,v in G.edges())
    U=G.to_undirected();bridges={frozenset(e) for e in nx.bridges(U)}
    assert all(frozenset((h,next(G.successors(h)))) in bridges for h in hybrids)
    # Ordinary graph dominance ignores parallel arc multiplicity and avoids
    # exponentially enumerating the same vertex route through serial bigons.
    dom=nx.immediate_dominators(nx.DiGraph(G),'R');common=set(G)
    for tip in taxa:
        chain={tip};v=tip
        while v!='R':v=dom[v];chain.add(v)
        common &= chain
    assert common=={'R'}
    assert not nx.check_planarity(nx.Graph(G))[0]
    W=U.copy();W.remove_edges_from([(u,v,k) for u,v,k in U.edges(keys=True) if frozenset((u,v)) in bridges])
    comps=list(nx.connected_components(W));two=[]
    for C in comps:
        ports=[(u,v) for u,v in G.edges() if (u in C) != (v in C)]
        H=[h for h in hybrids if h in C]
        assert len(H)<=len(ports)-(0 if 'R' in C else 1)
        if 'R' not in C and len(ports)==2:
            assert len(C)==2 and len(H)==1
            h=H[0];u=next(iter(C-{h}));assert G.number_of_edges(u,h)==2
            two.append((u,h))
    return hybrids,two

def clusters(G,taxa,bits):
    T=G.copy()
    for h in [v for v in G if G.in_degree(v)==2]:
        incoming=list(T.in_edges(h,keys=True));chosen=incoming[bits[h]]
        T.remove_edges_from([e for e in incoming if e!=chosen])
    C={frozenset(nx.descendants(T,v)&set(taxa)) for v in T}
    return C,{frozenset((c,frozenset(taxa)-c)) for c in C if 2<=len(c)<=len(taxa)-2}

def guard(cells,ages,hi,lo,cuts):
    L=len(cells);marks=set()
    for c in cuts:
        for i,(u,h) in enumerate(cells):
            if ages[h]<=c<=ages[u]:marks.add(i)
        for i in range(L+1):
            upper=hi if i==0 else ages[cells[i-1][1]]
            lower=lo if i==L else ages[cells[i][0]]
            if lower<c<upper:
                if i>0:marks.add(i-1)
                if i<L:marks.add(i)
    assert len(marks)<=2*len(cuts)
    i=0;runs=0
    while i<L:
        if i in marks:i+=1;continue
        first=i
        while i+1<L and i+1 not in marks:i+=1
        last=i;upper=hi if first==0 else ages[cells[first-1][1]]
        lower=lo if last==L-1 else ages[cells[last+1][0]]
        assert not any(lower<c<upper for c in cuts)
        runs+=1;i+=1
    assert runs<=2*len(cuts)+1
    return len(marks),runs

def main():
    rows=[];switchings=guards=0
    for cherry in (False,True):
        base_edges,taxa,_=old.source(cherry);base=nx.MultiDiGraph();base.add_edges_from(base_edges)
        for L in (1,2,7,40):
            G,taxa,ages,cells,hi,lo=insert_chain(cherry,L);hs,two=source_audit(G,taxa,ages)
            assert set(two)==set(cells)
            core=G.copy()
            for u,h in cells:
                a=next(core.predecessors(u));b=next(core.successors(h))
                core.remove_nodes_from([u,h]);core.add_edge(a,b)
            assert sorted(core.edges())==sorted(base.edges())
            r=sum(core.in_degree(v)==2 for v in core);n=len(taxa)
            assert r<=2*n-2 and len(core)<=6*n-5 and core.number_of_edges()<=8*n-8
            if L==40:assert len(hs)>2*n-2
            for vals in product((0,1),repeat=4):
                fixed=dict(zip(('H1','H2','H3','H4'),vals));truth=clusters(base,taxa,fixed)
                for pattern in (0,1,2):
                    bits=fixed|{h:(pattern if pattern<2 else i%2) for i,(_,h) in enumerate(cells)}
                    assert clusters(G,taxa,bits)==truth;switchings+=1
            cuts_list=[(),(F(1),F(2),F(3),F(4)),tuple(ages[u] for u,_ in cells[::3]),
                       tuple((ages[u]+ages[h])/2 for u,h in cells[::4])]
            for cuts in cuts_list:guard(cells,ages,hi,lo,cuts);guards+=1
            rows.append({'taxa':n,'original_hybrids':len(hs),'serial_bigons':L,'decorated_core_hybrids':r,
                         'nonplanar':True,'root_LSA':True,'all_hybrid_children_bridges':True})
    out={'status':'PASS','sources':rows,'displayed_switching_controls':switchings,'cut_guard_controls':guards,
         'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'fixture_sha256':hashlib.sha256(Path(old.__file__).read_bytes()).hexdigest(),
         'python':platform.python_version(),'networkx':nx.__version__,
         'scope':'Focused finite source/target/cut controls; all-size structural/approximation proof and full effective catalogue are separate.'}
    Path(__file__).with_name('nonplanar-g6-source-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
