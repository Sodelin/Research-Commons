"""Independent controls for the bounded-indegree HG, retaining original arc IDs.

This is finite corroboration of the hand theorem, not a genealogy-law inversion.
The decoder's population names are erased and its query size is enforced.
"""
from collections import defaultdict
from itertools import combinations, product
from pathlib import Path
import hashlib, json, platform, random, sys
import networkx as nx


def subsets(B, maximum=None):
    return [frozenset(U) for n in range(1, min(len(B), maximum or len(B))+1)
            for U in combinations(B, n)]


def partition_support(S, B):
    H = set()
    for positions in product(*(S[b] for b in B)):
        groups = defaultdict(set)
        for b, a in zip(B, positions): groups[a].add(b)
        H.add(frozenset(frozenset(g) for g in groups.values()))
    return H


def exact_candidate_truth(S, B, C):
    I = set.intersection(*(set(S[b]) for b in C))
    return any(all(any(v != a for v in S[b]) for b in set(B)-set(C)) for a in I)


class Observation:
    def __init__(self, B, k, loader):
        self.B, self.k, self.loader, self.cache = tuple(B), k, loader, {}

    def H(self, U):
        U = frozenset(U)
        assert 1 <= len(U) <= self.k+1
        if U not in self.cache: self.cache[U] = self.loader(tuple(sorted(U)))
        return self.cache[U]

    def possible(self, C):
        C = frozenset(C)
        return all(any((C & U) in p for p in self.H(U))
                   for U in subsets(self.B, self.k+1) if C & U)

    def sure(self, C):
        C = frozenset(C)
        return all(all(frozenset((b,c)) in p for p in self.H((b,c)))
                   for b,c in combinations(C, 2)) and all(
            all(frozenset((b,o)) not in p for p in self.H((b,o)))
            for b in C for o in set(self.B)-C)


def obstruction(S, B, C):
    """The anchor plus one blocking label per anchor value proof, constructive."""
    c0 = min(C); A = S[c0]; U = {c0}
    for a in A:
        inside = [c for c in C if a not in S[c]]
        if inside: U.add(min(inside))
        else:
            outside = [o for o in set(B)-C if S[o] == frozenset((a,))]
            assert outside
            U.add(min(outside))
    assert len(U) <= 1+len(A)
    assert not exact_candidate_truth(S, U, set(C)&U)
    return frozenset(U)


def abstract_controls():
    rng = random.Random(104729)
    counts = defaultdict(int)
    # Complete support-family census over a three-position universe, through
    # five labels for k=1,2 and through four labels for k=3.
    for k in (1,2,3):
        opts = subsets(tuple(range(3)), k)
        for n in range(1, (5 if k < 3 else 4)+1):
            B = tuple(range(n))
            for ds in product(opts, repeat=n):
                S = dict(zip(B, ds))
                obs = Observation(B,k,lambda U: partition_support(S,U))
                for C in subsets(B):
                    truth = exact_candidate_truth(S,B,C)
                    assert obs.possible(C) == truth
                    if not truth:
                        obstruction(S,B,C); counts['explicit_failure_witnesses'] += 1
                    counts['possible_block_tests'] += 1
                counts['complete_support_families'] += 1
    for k in (3,4,5):
        opts = subsets(tuple(range(7)), k)
        for n in (k+2, k+3):
            B = tuple(range(n))
            for _ in range(20):
                S = dict(zip(B,(rng.choice(opts) for _ in B)))
                # Literal partition support query, with caching. Bounded-size
                # probes remain small and no full partition oracle is used.
                obs = Observation(B,k,lambda U: partition_support(S,U))
                for C in rng.sample(subsets(B), min(30,2**n-1)):
                    truth = exact_candidate_truth(S,B,C)
                    assert obs.possible(C) == truth
                    if not truth:
                        obstruction(S,B,C);counts['explicit_failure_witnesses'] += 1
                    counts['possible_block_tests'] += 1
                counts['random_support_families'] += 1
    for k in range(1,7):
        # The k+1 abstract obstruction is sharp for local exact-block tests,
        # which is not a genealogy-law lower bound.
        B=tuple(range(k+1));C=frozenset((0,))
        S={0:frozenset(range(k))}|{i:frozenset((i-1,)) for i in range(1,k+1)}
        assert not exact_candidate_truth(S,B,C)
        for U in subsets(B,k):
            if U&C: assert exact_candidate_truth(S,U,U&C)
        counts['sharp_abstract_examples'] += 1
    return dict(counts)


def source(k, cherry=False, parallel=False):
    if parallel:
        # Includes two distinct parallel terminal parent arcs, and k active
        # original edge occurrences on every age in (5,10).
        E=[('R','Z'),('R','P0')];ages={'R':40,'Z':0,'H':5}
        for i in range(k-1):
            ages['P'+str(i)] = 30-i
            if i < k-2:E += [('P'+str(i),'H'),('P'+str(i),'P'+str(i+1))]
            else:E += [('P'+str(i),'H'),('P'+str(i),'H')]
        hs=('H',)
        if cherry:E += [('H','W'),('W','a'),('W','b')];ages['W']=2;leaves=('Z','a','b')
        else:E += [('H','a')];leaves=('Z','a')
    else:
        E=[('R','Z')]+list(zip('RABCDEFG','ABCDEFG'))
        ages=dict(zip('RABCDEFG',(30,27,24,21,18,15,12,9)))
        # Subdivide C->D, keeping the accepted K3,3-minor fixture and adding
        # extra H1 parents without increasing an ordinary node's outdegree.
        E.remove(('C','D'));last='C'
        for i in range(k-2):
            v='T'+str(i);ages[v]=21-(i+1)*3/(k-1)
            E += [(last,v),(v,'H1')];last=v
        E.append((last,'D'))
        for h,p,q in [('H1','A','E'),('H2','B','G'),('H3','C','F'),('H4','D','G')]:
            E += [(p,h),(q,h)];ages[h]=dict(H1=5,H2=6,H3=7,H4=8)[h]
        hs=('H1','H2','H3','H4')
        if cherry:E += [('H1','W'),('W','a1'),('W','a2')];ages['W']=2;leaves=('Z','a1','a2','b','c','d')
        else:E += [('H1','a')];leaves=('Z','a','b','c','d')
        E += [('H2','b'),('H3','c'),('H4','d')]
    ages.update({b:0 for b in leaves})
    # Keep arc IDs, even if endpoint pairs coincide.
    arcs=tuple((i,u,v) for i,(u,v) in enumerate(E))
    return arcs,leaves,ages,hs


def audit(arcs,leaves,ages,hs,k):
    G=nx.MultiDiGraph();G.add_edges_from((u,v,{'eid':i}) for i,u,v in arcs)
    assert nx.is_directed_acyclic_graph(G)
    assert set(nx.descendants(G,'R'))|{'R'}==set(G)
    for v in G:
        if v=='R':assert (G.in_degree(v),G.out_degree(v))==(0,2)
        elif v in leaves:assert (G.in_degree(v),G.out_degree(v))==(1,0)
        elif v in hs:assert 2<=G.in_degree(v)<=k and G.out_degree(v)==1
        else:assert (G.in_degree(v),G.out_degree(v))==(1,2)
    assert all(ages[u]>ages[v] for _,u,v in arcs)
    U=nx.MultiGraph();U.add_edges_from((u,v,{'eid':i}) for i,u,v in arcs)
    bridges=set()
    for i,u,v in arcs:
        V=nx.MultiGraph();V.add_edges_from((a,b) for j,a,b in arcs if j!=i)
        V.add_nodes_from(U)
        if not nx.has_path(V,u,v):bridges.add(i)
    assert all(next(i for i,u,v in arcs if u==h) in bridges for h in hs)
    # Independently exercise the replacement for the binary biconnected-blob
    # argument. The bridge-component quotient has exactly one rootward entry.
    W=nx.MultiGraph();W.add_nodes_from(U)
    W.add_edges_from((u,v) for i,u,v in arcs if i not in bridges)
    components=tuple(nx.connected_components(W))
    component={v:j for j,C in enumerate(components) for v in C}
    quotient=nx.DiGraph();quotient.add_nodes_from(range(len(components)))
    quotient.add_edges_from((component[u],component[v]) for i,u,v in arcs if i in bridges)
    assert nx.is_arborescence(quotient)
    assert quotient.in_degree(component['R'])==0
    assert all(quotient.in_degree(j)==1 for j in quotient if j!=component['R'])
    for h in hs:
        assert all(component[u]==component[h] for i,u,v in arcs if v==h)
        assert all(component[v]!=component[h] for i,u,v in arcs if u==h)
    # The root is LSA since its direct Z branch avoids every other vertex.
    assert ('R','Z') in [(u,v) for _,u,v in arcs]
    nonplanar=not nx.check_planarity(nx.Graph(U))[0]
    return bridges,nonplanar


def routes(arcs,tip,force=None):
    if tip=='R':return ((),)
    parents=[(i,u,v) for i,u,v in arcs if v==tip]
    if force is not None and tip in force:parents=[force[tip]]
    return tuple((e,)+p for e in parents for p in routes(arcs,e[1],force))


def position(path,t,ages):
    active=[i for i,u,v in path if ages[v]<=t<ages[u]]
    if t>=ages['R']:assert not active;return 'ancestral'
    assert len(active)==1
    return active[0]


def assignment_support(arcs,hs,B,t,ages,mode):
    if mode=='common':
        options=[[e for e in arcs if e[2]==h] for h in hs]
        assignments=(tuple(position(routes(arcs,b,dict(zip(hs,cs)))[0],t,ages) for b in B)
                     for cs in product(*options))
    else:
        assignments=(tuple(position(p,t,ages) for p in ps)
                     for ps in product(*(routes(arcs,b) for b in B)))
    return set(assignments)


def supported_partitions(arcs,hs,B,t,ages,mode):
    H=set()
    for assignment in assignment_support(arcs,hs,B,t,ages,mode):
        g=defaultdict(set)
        for b,p in zip(B,assignment):g[p].add(b)
        H.add(frozenset(frozenset(U) for U in g.values()))
    return H


def source_controls():
    rows=[];position_tests=cartesian_tests=chronology_cases=0
    for k in (2,3,4,5):
        for parallel in (False,True):
            for cherry in (False,True):
                arcs,A,ages,hs=source(k,cherry,parallel)
                bridges,nonplanar=audit(arcs,A,ages,hs,k)
                if not parallel:assert nonplanar
                grid=sorted(set(ages.values()))
                probes=sorted(set(grid+[ (x+y)/2 for x,y in zip(grid,grid[1:])]))
                peak=0
                for b in A:
                    for t in probes:
                        positions={position(p,t,ages) for p in routes(arcs,b)}
                        assert 1<=len(positions)<=k
                        peak=max(peak,len(positions));position_tests+=1
                assert peak==k
                truth=set.union(*(set.union(*(set(p) for p in supported_partitions(arcs,hs,A,t,ages,'common')))
                                  for t in grid))
                for mode in ('common','independent'):
                    B=tuple(A);groups={b:frozenset((b,)) for b in B};s=0;recorded=set();rounds=0
                    while len(B)>1:
                        for tau in (t for t in grid if t>=s):
                            obs=Observation(B,k,lambda U: supported_partitions(arcs,hs,U,tau,ages,mode))
                            sure={C for C in subsets(B) if len(C)>1 and obs.sure(C)}
                            if sure:break
                        else:raise AssertionError('No attained sure block')
                        for t in (t for t in grid if s<=t<=tau):
                            domains={b:{position(p,t,ages) for p in routes(arcs,b)} for b in B}
                            actual=assignment_support(arcs,hs,B,t,ages,mode)
                            assert actual==set(product(*(domains[b] for b in B)));cartesian_tests+=1
                            obs=Observation(B,k,lambda U: supported_partitions(arcs,hs,U,t,ages,mode))
                            possible={C for C in subsets(B) if obs.possible(C)}
                            actual_blocks=set.union(*(set(p) for p in supported_partitions(arcs,hs,B,t,ages,mode)))
                            assert possible==actual_blocks
                            for C in possible:recorded.add(frozenset().union(*(groups[b] for b in C)))
                        for C in sure:
                            b=min(C);groups[b]=frozenset().union(*(groups[c] for c in C))
                            for c in C-{b}:del groups[c]
                        B=tuple(sorted(groups));s=tau;rounds+=1
                        assert rounds<=len(A)-1
                    recorded.add(frozenset(A))
                    assert recorded==truth
                    chronology_cases+=1
                rows.append({'k':k,'parallel_arcs':parallel,'cherry':cherry,'taxa':len(A),
                             'nonplanar':nonplanar,'original_arc_count':len(arcs),
                             'bridge_count':len(bridges),'max_observed_position_count':peak})
    return {'sources':rows,'original_tip_time_position_checks':position_tests,
            'safe_stage_Cartesian_assignment_checks':cartesian_tests,
            'full_X_k_plus_1_query_chronology_cases':chronology_cases}


if __name__=='__main__':
    result={'status':'PASS','source':source_controls(),
            'versions':{'python':platform.python_version(),'networkx':nx.__version__},
            'scope':'Finite support controls only; no arbitrary-law germ inversion or statistical lower bound.'}
    if '--source-only' not in sys.argv: result['abstract']=abstract_controls()
    p=Path(__file__)
    result['checker_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
    name='bounded-indegree-source-results.json' if '--source-only' in sys.argv else 'bounded-indegree-support-results.json'
    p.with_name(name).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
