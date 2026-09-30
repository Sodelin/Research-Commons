"""Exact finite controls. Graph routines follow the standard edge-cut method
also used in ROOT-EXACT-QUERY-20260930/verify_candidate_order.py. This is a
new implementation, not a byte-identical copy or an independent peer review.
"""
from itertools import combinations, permutations, product
from functools import lru_cache


def edge(a,b):
    return tuple(sorted((a,b)))


def tree_splits(edges, taxa):
    taxa=set(taxa)
    adj={}
    for a,b in edges:
        adj.setdefault(a,set()).add(b); adj.setdefault(b,set()).add(a)
    seen=set(); todo=[next(iter(adj))]
    while todo:
        a=todo.pop()
        if a in seen: continue
        seen.add(a); todo.extend(adj[a]-seen)
    assert seen==set(adj) and len(edges)==len(adj)-1
    out=set()
    for a,b in edges:
        seen={a}; todo=[a]
        while todo:
            u=todo.pop()
            for v in adj[u]:
                if (u==a and v==b) or (u==b and v==a) or v in seen: continue
                seen.add(v);todo.append(v)
        side=frozenset(seen & taxa)
        other=frozenset(taxa-side)
        if min(len(side),len(other))>=2:
            out.add(min(side,other,key=lambda t:(len(t),tuple(sorted(t)))))
    return frozenset(out)


def restrict_splits(splits, taxa):
    taxa=set(taxa); out=set()
    for side in splits:
        a=frozenset(set(side)&taxa); b=frozenset(taxa-set(a))
        if min(len(a),len(b))>=2:
            out.add(min(a,b,key=lambda t:(len(t),tuple(sorted(t)))))
    return frozenset(out)


def quartet_mask(splits, q):
    a,b,c,d=sorted(q); ans=0
    for s in splits:
        pair=frozenset(set(q)&set(s))
        if len(pair)!=2: continue
        if a not in pair: pair=frozenset(set(q)-set(pair))
        ans |= {frozenset((a,b)):1, frozenset((a,c)):2, frozenset((a,d)):4}[pair]
    return ans


def pair_bit(q,pair):
    a,b,c,d=sorted(q); pair=frozenset(pair)
    if a not in pair: pair=frozenset(set(q)-set(pair))
    return {frozenset((a,b)):1, frozenset((a,c)):2, frozenset((a,d)):4}[pair]


def circular(side,order):
    side=set(side)
    return sum((order[i] in side)!=(order[(i+1)%len(order)] in side) for i in range(len(order)))<=2


def common_order(splits,order):
    return all(circular(s,order) for s in splits)


def circular_orders(taxa):
    taxa=sorted(taxa)
    for tail in permutations(taxa[1:]):
        if len(tail)>1 and tail[0]>tail[-1]: continue
        yield (taxa[0],)+tail


def insert(order,z,i):
    return order[:i+1]+(z,)+order[i+1:]


def valid_gaps(splits,order,z):
    return {i for i in range(len(order)) if common_order(splits,insert(order,z,i))}


def binary_trees(n):
    out=[frozenset((edge(-1,0),edge(-1,1),edge(-1,2)))]
    for leaf in range(3,n):
        node=-(leaf-1); nxt=[]
        for graph in out:
            for u,v in sorted(graph):
                nxt.append(frozenset((graph-{edge(u,v)}) | {edge(u,node),edge(v,node),edge(node,leaf)}))
        out=nxt
    return out


@lru_cache(None)
def ordered_shapes(leaves):
    leaves=tuple(leaves)
    if len(leaves)==1: return (leaves[0],)
    out=[]
    for i in range(1,len(leaves)):
        for l in ordered_shapes(leaves[:i]):
            for r in ordered_shapes(leaves[i:]): out.append((l,r))
    return tuple(out)


def shape_graph(shape):
    """Rooted binary shape with occurrence tip integer labels; root degree 2."""
    edges=[]; nextid=-1
    def walk(t):
        nonlocal nextid
        if isinstance(t,int):return t
        me=nextid; nextid-=1
        for child in t: edges.append(edge(me,walk(child)))
        return me
    walk(shape)
    return frozenset(edges)


def occurrence_union(shape,labels):
    g=shape_graph(shape); labels=tuple(labels)
    positions={l:tuple(i for i,x in enumerate(labels) if x==l) for l in set(labels)}
    all_splits=tree_splits(g,range(len(labels)))
    # Include all physical edges' singleton cuts: two selected occurrences of
    # different taxa cannot lie on a physical singleton, so internal cuts suffice.
    out=set()
    for chosen in product(*(positions[l] for l in sorted(positions))):
        selected=set(chosen); remap={i:labels[i] for i in chosen}
        for s in restrict_splits(all_splits,selected):
            a=frozenset(remap[x] for x in s); b=frozenset(positions.keys()-a)
            out.add(min(a,b,key=lambda t:(len(t),tuple(sorted(t)))))
    return frozenset(out)


def filter_gaps(order,z,cuts,answer,candidates):
    """Remove gaps whose induced quartet crossing is present; O(|G|) work."""
    i,j,k=sorted(cuts)
    q=tuple(sorted((z,order[i],order[j],order[k])))
    bits=(pair_bit(q,(z,order[k])),pair_bit(q,(z,order[i])),pair_bit(q,(z,order[j])))
    return {g for g in candidates if not answer & bits[0 if i<=g<j else 1 if j<=g<k else 2]}
