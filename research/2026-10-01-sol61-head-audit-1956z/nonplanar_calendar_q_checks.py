"""Finite source/route checks for the nonplanar G5 Q-only extension.

All positive routes survive conditioning on no selected merger. This checks
their support/chronological lifting, not recovery of an analytic germ from data.
"""
import json,platform
from itertools import combinations,product
from collections import defaultdict
from pathlib import Path
import networkx as nx

def source(cherry):
    edges=[('R','Z')]+list(zip('RABCDEFG','ABCDEFG'))
    for h,a,b in [('H1','A','E'),('H2','B','G'),('H3','C','F'),('H4','D','G')]:
        edges.extend([(a,h),(b,h)])
    if cherry:
        edges.extend([('H1','W'),('W','a1'),('W','a2')])
        leaves=('Z','a1','a2','b','c','d')
    else:
        edges.append(('H1','a'));leaves=('Z','a','b','c','d')
    edges.extend([('H2','b'),('H3','c'),('H4','d')])
    ages={'R':30,'A':27,'B':24,'C':21,'D':18,'E':15,'F':12,'G':9,
          'H1':5,'H2':6,'H3':7,'H4':8,'W':2}
    ages.update({x:0 for x in leaves})
    return edges,leaves,ages

def audit(edges,leaves,ages):
    G=nx.DiGraph(edges);U=nx.Graph(edges)
    assert nx.is_directed_acyclic_graph(G)
    assert set(nx.descendants(G,'R'))|{'R'}==set(G)
    hs=[]
    for v in G:
        deg=(G.in_degree(v),G.out_degree(v))
        if v=='R':assert deg==(0,2)
        elif v in leaves:assert deg==(1,0)
        elif deg==(2,1):hs.append(v)
        else:assert deg==(1,2)
    assert all(ages[u]>ages[v] for u,v in edges)
    bridges={frozenset(e) for e in nx.bridges(U)}
    assert all(frozenset((h,next(G.successors(h)))) in bridges for h in hs)
    # Direct root->Z and all other root->tip paths have no stable common
    # nonroot vertex, so the original root is LSA.
    for v in set(G)-{'R'}:
        assert any(any(v not in path for path in nx.all_simple_paths(G,'R',tip)) for tip in leaves)
    assert not nx.check_planarity(U)[0]
    # Explicit K3,3 minor: remove pendant tips/root, suppress each hybrid,
    # and contract A--B. No planarity oracle alone supplies this witness.
    core=nx.Graph();core.add_edges_from(list(zip('ABCDEFG','BCDEFG')))
    core.add_edges_from([('A','E'),('B','G'),('C','F'),('D','G')])
    minor=nx.contracted_nodes(core,'B','A',self_loops=False)
    assert set(minor)==set('BCDEFG')
    assert {frozenset(e) for e in minor.edges}=={frozenset((x,y)) for x in 'BDF' for y in 'CEG'}
    return G,tuple(sorted(hs))

def paths(G,tip,force=None):
    if tip=='R':return [()]
    parents=tuple(G.predecessors(tip))
    if len(parents)==2 and force is not None:parents=(parents[force[tip]],)
    return tuple(((u,tip),)+p for u in parents for p in paths(G,u,force))

def populations(path,t,ages):
    active=[e for e in path if ages[e[1]]<=t<ages[e[0]]]
    if t>=ages['R']:assert not active;return ('ANCESTRAL','R')
    assert len(active)==1
    return active[0]

def support(G,hs,B,t,ages,mode):
    if mode=='common':
        routes=[tuple(paths(G,b,dict(zip(hs,bits)))[0] for b in B) for bits in product((0,1),repeat=len(hs))]
    else:routes=product(*(paths(G,b) for b in B))
    result=set()
    for rs in routes:
        groups=defaultdict(list)
        for b,p in zip(B,rs):groups[populations(p,t,ages)].append(b)
        result.add(frozenset(frozenset(g) for g in groups.values()))
    return result

def chronology(G,hs,A,ages,mode):
    B=tuple(A);groups={b:frozenset((b,)) for b in B};s=0
    grid=sorted(set(ages.values()))
    recorded={frozenset((b,)) for b in A}|{frozenset(A)}
    rounds=0
    while len(B)>1:
        for tau in (t for t in grid if t>=s):
            H=support(G,hs,B,tau,ages,mode)
            sure=set.intersection(*(set(p) for p in H))
            sure={g for g in sure if len(g)>1}
            if sure:break
        else:raise AssertionError('no attained sure-block time')
        for t in (t for t in grid if s<=t<=tau):
            for partition in support(G,hs,B,t,ages,mode):
                for block in partition:recorded.add(frozenset().union(*(groups[b] for b in block)))
        new=dict(groups)
        for block in sure:
            representative=min(block)
            new[representative]=frozenset().union(*(groups[b] for b in block))
            for b in block-{representative}:del new[b]
        groups=new;B=tuple(sorted(new));s=tau;rounds+=1
        assert rounds<=len(A)-1
    return recorded,rounds

def main():
    sources=[];cases=0;false_raw=0;full_cases=0
    for cherry in (False,True):
        edges,leaves,ages=source(cherry);G,hs=audit(edges,leaves,ages)
        rounds=[]
        for A in combinations(leaves,4):
            truth={frozenset((b,)) for b in A}|{frozenset(A)}
            for t in sorted(set(ages.values())):
                for partition in support(G,hs,A,t,ages,'common'):truth.update(partition)
            raw=set()
            for t in sorted(set(ages.values())):
                for partition in support(G,hs,A,t,ages,'independent'):raw.update(partition)
            if raw-truth:false_raw+=1
            for mode in ('common','independent'):
                recovered,n=chronology(G,hs,A,ages,mode)
                assert recovered==truth
                # A resolved unrooted quartet is witnessed by a recovered
                # rooted cluster containing exactly two of its four labels.
                q={frozenset((c,frozenset(A)-c)) for c in recovered if len(c)==2}
                qt={frozenset((c,frozenset(A)-c)) for c in truth if len(c)==2}
                assert q==qt
                cases+=1;rounds.append(n)
        full_truth={frozenset((b,)) for b in leaves}|{frozenset(leaves)}
        for t in sorted(set(ages.values())):
            for partition in support(G,hs,leaves,t,ages,'common'):full_truth.update(partition)
        for mode in ('common','independent'):
            full_recovered,_=chronology(G,hs,leaves,ages,mode)
            assert full_recovered==full_truth
            full_s={frozenset((c,frozenset(leaves)-c)) for c in full_recovered if 2<=len(c)<=len(leaves)-2}
            truth_s={frozenset((c,frozenset(leaves)-c)) for c in full_truth if 2<=len(c)<=len(leaves)-2}
            assert full_s==truth_s;full_cases+=1
        sources.append({'taxa':len(leaves),'hybrids':len(hs),'vertices':len(G),'edges':len(edges),
                        'underlying_graph':'nonplanar, explicit K3,3 minor',
                        'root_LSA':True,'all_hybrid_child_edges_bridges':True,
                        'strict_positive_calendar':True,'max_lifting_rounds':max(rounds)})
    assert false_raw>0
    report={'status':'PASS','sources':sources,'quartet_mechanism_lifting_cases':cases,'full_sample_cluster_and_split_cases':full_cases,
            'independent_raw_block_union_false_positive_cases':false_raw,
            'versions':{'python':platform.python_version(),'networkx':nx.__version__},
            'scope':'Exact finite graph/positive-route-support controls, not finite-data germ inversion, all-size execution, or Lean completion.'}
    out=Path(__file__).with_name('nonplanar-calendar-q-results.json');out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
