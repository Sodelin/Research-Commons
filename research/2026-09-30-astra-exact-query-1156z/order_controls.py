"""Graph-derived tests of the adaptive all-order-space invariant."""
from core import *
from adaptive_order import AdaptiveOrderLearner
from pathlib import Path
import json,platform,random


def test_instance(splits,n,labels=None,check_every=True):
    if labels is None:labels=tuple(range(n))
    qs={}
    def oracle(q):
        qs[q]=quartet_mask(splits,q);return qs[q]
    learner=AdaptiveOrderLearner(labels,oracle)
    def check(a):
        taxa=a.tree.taxa;ss=restrict_splits(splits,taxa)
        actual={c for c in circular_orders(taxa) if common_order(ss,c)}
        obtained=a.tree.all_orders()
        assert obtained==actual,('order language mismatch',n,labels,ss,obtained,actual,a.history)
        # Check that each maintained internal edge is displayed in every
        # original tree separately in tests supplying that information later.
    learner.run(check if check_every else None)
    assert common_order(splits,learner.tree.one_order())
    assert sum(h['central_nodes'] for h in learner.history)<=n-3
    return learner


def small_families():
    rows=[]
    for n in (4,5,6):
        ts=[tree_splits(g,range(n)) for g in binary_trees(n)]
        unions=set(ts)
        if n<=5:
            for t in ts:unions.update(a|t for a in list(unions))
        else:unions.update(a|b for a,b in combinations(ts,2))
        orders=list(circular_orders(range(n)))
        row={'n':n,'all_considered_unions':len(unions),'circular_unions':0,'runs':0,'max_queries':0,'max_central_visits':0}
        for ss in sorted(unions,key=lambda x:repr(sorted(map(sorted,x)))):
            if not any(common_order(ss,c) for c in orders):continue
            row['circular_unions']+=1
            # Two insertion orders on every fixture; all labels arbitrary.
            for labels in (tuple(range(n)),tuple(reversed(range(n)))):
                a=test_instance(ss,n,labels)
                row['runs']+=1;row['max_queries']=max(row['max_queries'],len(a.cache))
                row['max_central_visits']=max(row['max_central_visits'],sum(h['central_nodes'] for h in a.history))
        rows.append(row)
    return rows


def random_shape(leaves,rng):
    if len(leaves)==1:return leaves[0]
    i=rng.randrange(1,len(leaves));return (random_shape(leaves[:i],rng),random_shape(leaves[i:],rng))


def occurrences():
    rng=random.Random(1156);rows=[]
    for n in (5,6,7,8):
        row={'n':n,'instances':0,'runs':0,'max_queries':0,'max_central_visits':0,'largest_copy_count':0}
        for k in range(80):
            copies=[1+rng.randrange(2) for _ in range(n)]
            labels=tuple(x for x,c in enumerate(copies) for _ in range(c))
            shape=(0,random_shape(tuple(range(1,len(labels))),rng))
            ss=occurrence_union(shape,labels)
            assert common_order(ss,tuple(range(n)))
            ordering=list(range(n));rng.shuffle(ordering)
            a=test_instance(ss,n,tuple(ordering))
            row['instances']+=1;row['runs']+=1
            row['max_queries']=max(row['max_queries'],len(a.cache))
            row['max_central_visits']=max(row['max_central_visits'],sum(h['central_nodes'] for h in a.history))
            row['largest_copy_count']=max(row['largest_copy_count'],sum(c==2 for c in copies))
        rows.append(row)
    return rows

if __name__=='__main__':
    result={'status':'PASS','python':platform.python_version(),'small_family_rows':small_families(),'occurrence_rows':occurrences(),
            'limits':'Finite author controls, not independent review, formal proof or a census of source-admitted graphs. Occurrence controls use the inherited paired-tip representation.'}
    text=json.dumps(result,indent=2)+'\n';Path(__file__).with_name('ORDER-CHECKS.json').write_text(text);print(text)
