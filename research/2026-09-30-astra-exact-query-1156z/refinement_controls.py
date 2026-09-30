"""Challenge the common-refinement invariant using actual separate trees.
The oracle is independently generated from graph BFS distances. Split cuts
and the independently authored affine decoder provide separate controls.
"""
from core import *
from adaptive_order import AdaptiveOrderLearner
from order_controls import random_shape
from recover_all import sparse_provider,reference_provider,order_bound
from pathlib import Path
import json,platform,random


def run():
    rng=random.Random(30115699);p=sparse_provider();rows=[];allprefix=0;alltreechecks=0
    for n,instances in ((7,100),(8,100),(10,100),(16,80),(32,40)):
        row={'n':n,'families':0,'prefixes':0,'individual_tree_refinement_checks':0,'max_order_queries':0,'max_family_size':0}
        for trial in range(instances):
            count=rng.choice((1,2,3,5,8,16,32));trees=[];oracles=[]
            for j in range(count):
                shape=random_shape(tuple(range(1,n)),rng)
                graph=p.graph_from_shape(shape,n)
                edges={edge(u,v) for u,ns in graph.items() for v in ns}
                trees.append(tree_splits(edges,range(n)))
                oracles.append(p.physical_quartet_oracle(graph,[[i] for i in range(n)]))
            union=frozenset().union(*trees)
            def oracle(q):
                value=0
                for provider in oracles:value |= provider(q)
                assert value==quartet_mask(union,q)
                return value
            labels=list(range(n));rng.shuffle(labels)
            learner=AdaptiveOrderLearner(labels,oracle)
            def check(a):
                taxa=a.tree.taxa
                edges={edge(u,v) for u,ns in a.tree.rot.items() for v in ns}
                required=tree_splits(edges,taxa)
                for ts in trees:
                    assert required<=restrict_splits(ts,taxa),('common refinement failed',n,trial,taxa,required,ts)
                    row['individual_tree_refinement_checks']+=1
                if n<=8:
                    truth={c for c in circular_orders(taxa) if common_order(restrict_splits(union,taxa),c)}
                    assert a.tree.all_orders()==truth
                row['prefixes']+=1
            learner.run(check)
            reference=reference_provider().learn_order(n,oracle)
            assert reference.independent_orientations==len(learner.tree.rot)-n
            assert len(learner.cache)<=order_bound(n)
            assert sum(h['central_nodes'] for h in learner.history)==n-2-(len(learner.tree.rot)-n)
            row['families']+=1;row['max_family_size']=max(row['max_family_size'],count)
            row['max_order_queries']=max(row['max_order_queries'],len(learner.cache))
        rows.append(row)
    return rows

if __name__=='__main__':
    r={'status':'PASS','python':platform.python_version(),'seed':30115699,'rows':run(),
       'limits':'Author controls of arbitrary circular binary-tree families; not a source network census, independent reviewer execution, or formal proof. BFS oracle, edge cuts and unchanged peer affine decoder are distinct calculations. Validation queries are separate from learner counts.'}
    text=json.dumps(r,indent=2)+'\n';Path(__file__).with_name('REFINEMENT-CHECKS.json').write_text(text);print(text)
