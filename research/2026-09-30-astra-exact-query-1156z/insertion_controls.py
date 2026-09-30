"""All-size proof controls, not proof by enumeration. Standard library only."""
from core import *
from pathlib import Path
import json, platform


from insertion import reduced_gap_candidates, learn_all_gaps


def cached_query(splits):
    cache={}
    def q(taxa):
        taxa=tuple(sorted(taxa))
        if taxa not in cache:cache[taxa]=quartet_mask(splits,taxa)
        return cache[taxa]
    return q,cache


def validate_rooted(directed,taxa,hybrids):
    vs=set().union(*(set(e) for e in directed)); parents={v:set() for v in vs}; children={v:set() for v in vs}
    for a,b in directed:parents[b].add(a);children[a].add(b)
    roots=[v for v in vs if not parents[v]];assert len(roots)==1;root=roots[0]
    for v in vs:
        expected=(0,2) if v==root else ((1,0) if v in taxa else ((2,1) if v in hybrids else (1,2)))
        assert (len(parents[v]),len(children[v]))==expected
    todo=[root]; topo=[]
    while todo:
        v=todo.pop()
        if v in topo:continue
        if not parents[v]<=set(topo):continue
        topo.append(v);todo.extend(children[v])
    assert len(topo)==len(vs)
    dom={root:{root}}
    for v in topo[1:]:dom[v]={v}|set.intersection(*(dom[p] for p in parents[v]))
    assert set.intersection(*(dom[t] for t in taxa))=={root}
    return {'vertices':len(vs),'edges':len(directed),'binary_DAG_LSA':True}


def pentagon():
    # r=0,b=1,c=2,a=3,z=4; hybrid -1, ordinary -2..-5, root -6.
    directed={(-6,-3),(-6,-4),(-3,2),(-3,-2),(-2,3),(-2,-1),(-4,0),(-4,-5),(-5,1),(-5,-1),(-1,4)}
    admission=validate_rooted(directed,set(range(5)),{-1})
    # Underlying graph: one five-cycle (-1,-2,-3,-4,-5), with
    # (-3,-4) subdivided by root -6; pendant tips at every cycle vertex.
    # Suppressing -6 restores that cycle. This explicit embedding has all
    # taxa on its outer face; the sole hybrid child is a pendant bridge.
    unions=[]
    for deleted in [(-2,-1),(-5,-1)]:
        g=frozenset(edge(a,b) for a,b in directed-{deleted})
        unions.append(tree_splits(g,range(5)))
    union=frozenset().union(*unions)
    old=(0,1,2,3); true=(0,1,4,3,2)
    assert restrict_splits(union,range(4))==frozenset((frozenset((0,1)),))
    assert common_order(restrict_splits(union,range(4)),old)
    assert common_order(union,true)
    assert not valid_gaps(union,old,4)
    q,cache=cached_query(union)
    assert not learn_all_gaps(old,4,q)
    return {'admission':admission,'directed_edges':sorted(directed),
            'displayed_tree_splits':[[sorted(s) for s in sorted(ss,key=lambda x:tuple(sorted(x)))] for ss in unions],
            'old_order':old,'full_compatible_order':true,'valid_insertion_gaps':[],
            'quartet_support':{','.join(map(str,q)):quartet_mask(union,q) for q in combinations(range(5),4)},
            'limits':'Explicit unicyclic outer-face argument; no general network-validator import.'}


def exhaustive():
    rows=[]
    for n in (4,5,6):
        ts=[tree_splits(g,range(n)) for g in binary_trees(n)]
        # Enumerate all family split unions at n<=5, and singleton/pair
        # unions at n=6. Duplicated outputs are deliberately deduplicated.
        unions=set(ts)
        if n<=5:
            for t in ts: unions.update(a|t for a in list(unions))
        else:
            unions.update(a|b for a,b in combinations(ts,2))
        z=n-1; orders=list(circular_orders(range(n-1)))
        counts={'n':n,'unions':len(unions),'compatible_restrictions':0,'empty_extension':0,
                'promised_cases':0,'general_max_queries':0,'promised_max_queries':0}
        for ss in unions:
            oldss=restrict_splits(ss,range(n-1))
            for order in orders:
                if not common_order(oldss,order):continue
                # May have no common full order; general theorem still applies.
                truth=valid_gaps(ss,order,z)
                assert len(truth)<=2
                q,cache=cached_query(ss)
                got=learn_all_gaps(order,z,q)
                assert got==truth,(n,ss,order,truth,got)
                counts['compatible_restrictions']+=1
                counts['empty_extension']+=not truth
                counts['general_max_queries']=max(counts['general_max_queries'],len(cache))
                if truth:
                    q,cache=cached_query(ss)
                    got=learn_all_gaps(order,z,q,promised=True)
                    assert got==truth,(n,ss,order,truth,got)
                    counts['promised_cases']+=1
                    counts['promised_max_queries']=max(counts['promised_max_queries'],len(cache))
        rows.append(counts)
    return rows

if __name__=='__main__':
    result={'status':'PASS','python':platform.python_version(),'pentagon':pentagon(),'tree_family_controls':exhaustive(),
            'scope':'Exact graph-cut controls of all binary-tree-family unions at n=4,5 and singleton/pair unions at n=6; all compatible restricted orders.',
            'limits':'Finite controls by theorem author, not independent review or formal verification.'}
    text=json.dumps(result,indent=2)+'\n'
    Path(__file__).with_name('INSERTION-CHECKS.json').write_text(text)
    print(text)
