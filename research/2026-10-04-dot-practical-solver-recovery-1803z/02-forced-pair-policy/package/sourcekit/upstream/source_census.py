"""Complete finite rooted source census for a complete original-ID registry.

Admitted class: binary rooted DAG, root is LSA of all sampled leaf taxa,
each hybrid's child edge is an undirected cut edge, and a plane embedding
exists with all taxon leaves on one face. Parallel arcs are retained.
This uses the cut-child definition of galledness in the Commons contract,
not the more restrictive disjoint-cycle definition of a galled tree.

Enumeration is finite but highly exponential. No hidden-ID bound is added:
`r` must be the COMPLETE number of original hybrid IDs supplied by contract.
Requires networkx and the companion law_compiler module.
"""
from __future__ import annotations
from itertools import permutations, product
from collections import defaultdict
from law_compiler import Network, forest, split_signature
import networkx as nx


def reachable(edges, start, removed_vertex=None, omitted_edge=None, undirected=False):
    adj = defaultdict(list)
    for i, (u, v) in enumerate(edges):
        if i == omitted_edge or removed_vertex in (u, v):
            continue
        adj[u].append(v)
        if undirected:
            adj[v].append(u)
    visited = set() if start == removed_vertex else {start}
    todo = list(visited)
    while todo:
        u = todo.pop()
        for v in adj[u]:
            if v not in visited:
                visited.add(v); todo.append(v)
    return visited


def cofacial(edges, marked):
    """Apex planarity test; subdivide edges to preserve parallel-edge topology."""
    graph = nx.Graph()
    for i, (u, v) in enumerate(edges):
        mid = ('edge', i)
        graph.add_edge(('vertex', u), mid)
        graph.add_edge(mid, ('vertex', v))
    for v in marked:
        graph.add_edge(('apex',), ('vertex', v))
    return nx.check_planarity(graph)[0]


def admitted(net: Network) -> bool:
    try:
        inc, out, order, hybrids = net.structure()
    except ValueError:
        return False
    # A non-root vertex may not dominate every sampled taxon.
    for v in order:
        if v != net.root and not (set(net.leaves) & reachable(net.edges, net.root, removed_vertex=v)):
            return False
    for h in hybrids:
        e = out[h][0]
        child = net.edges[e][1]
        if child in reachable(net.edges, h, omitted_edge=e, undirected=True):
            return False
    return cofacial(net.edges, net.leaves)


def canonical_key(net: Network) -> tuple:
    """Isomorphism key preserving root, leaves, hybrid IDs AND parent labels."""
    inc, _, order, hybrids = net.structure()
    trees = sorted(set(order)-{net.root}-set(net.leaves)-set(hybrids))
    keys=[]
    for perm in permutations(range(len(trees))):
        names={net.root:('R',0)}
        names.update({v:('T',j) for v,j in zip(trees,perm)})
        names.update({v:('H',v) for v in hybrids})
        names.update({v:('L',v) for v in net.leaves})
        keys.append(tuple(sorted((names[u],names[v],inc[v].index(e) if v in hybrids else -1)
                                 for e,(u,v) in enumerate(net.edges))))
    return min(keys)


def census(n: int, r: int):
    """Yield exactly all admitted isomorphism types (including edge-label data).

    Tree-internal labels are dummy IDs, hybrid H0,... and leaf L0,... are fixed.
    Ordered parent selection at a hybrid preserves original 0/1 direction.
    Topological-order duplicates are removed only by the exact canonical key.
    """
    if not isinstance(n,int) or not isinstance(r,int) or n<2 or r<0:
        raise ValueError('Require n>=2 and r>=0 integers.')
    leaves=tuple(f'L{i}' for i in range(n))
    t=n+r-2
    seen=set()
    def finish(edges, caps, leaf_index):
        if leaf_index == n:
            if any(caps.values()):
                raise AssertionError('Unfilled parent stubs at census leaf stage.')
            net=Network(tuple(edges),'R',leaves)
            key=canonical_key(net)
            if key not in seen:
                seen.add(key)
                if admitted(net):
                    yield net
            return
        for parent in sorted(caps):
            if caps[parent]>0:
                nc=dict(caps); nc[parent]-=1
                yield from finish(edges+[(parent,leaves[leaf_index])],nc,leaf_index+1)
    def internal(edges,caps,tree_count,unplaced):
        if tree_count==t and not unplaced:
            yield from finish(edges,caps,0)
            return
        options=[]
        if tree_count<t:
            options.append((f'T{tree_count}',1,2,tree_count+1,unplaced))
        options.extend((h,2,1,tree_count,tuple(x for x in unplaced if x!=h)) for h in unplaced)
        for node,indeg,outdeg,nt,nh in options:
            parents=sorted(p for p,c in caps.items() if c>0)
            for chosen in product(parents,repeat=indeg):
                need={p:chosen.count(p) for p in set(chosen)}
                if any(need[p]>caps[p] for p in need):
                    continue
                nc=dict(caps)
                for p,k in need.items(): nc[p]-=k
                nc[node]=outdeg
                yield from internal(edges+[(p,node) for p in chosen],nc,nt,nh)
    yield from internal([],{'R':2},0,tuple(f'H{i}' for i in range(r)))


def displayed(net: Network) -> dict:
    """Compute each original complete switching's unrooted split signature."""
    inc,out,_,hybrids=net.structure()
    answers={}
    for bits in product((0,1),repeat=len(hybrids)):
        discarded={inc[h][1-b] for h,b in zip(hybrids,bits)}
        def descend(v):
            if v in net.leaves: return v
            children=[descend(net.edges[e][1]) for e in out[v] if e not in discarded]
            children=[x for x in children if x is not None]
            if not children: return None
            if len(children)==1: return children[0]
            if len(children)!=2: raise AssertionError('Nonbinary switching.')
            return forest(children)
        answers[bits]=split_signature(descend(net.root))
    return answers

if __name__=='__main__':
    import argparse,json,time
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('n',type=int); p.add_argument('r',type=int)
    args=p.parse_args()
    start=time.monotonic()
    nets=list(census(args.n,args.r))
    print(json.dumps({'n':args.n,'r':args.r,'admitted_graphs':len(nets),
                      'distinct_switching_target_sets':len({tuple(sorted(set(displayed(g).values()))) for g in nets}),
                      'seconds':time.monotonic()-start},indent=2))
