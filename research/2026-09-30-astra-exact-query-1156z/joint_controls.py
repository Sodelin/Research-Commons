"""Executed cross-author integration and graph/BFS controls.
Reference validation queries are separate, NOT charged to the new learner.
"""
from core import *
from recover_all import *
from order_controls import random_shape
from insertion_controls import pentagon
from pathlib import Path
import json,platform,random,math,hashlib
from datetime import datetime,timezone


def relabel_tests():
    count=0
    for perm in permutations(range(4)):
        for mask in range(8):
            obtained=remap_answer(perm,(0,1,2,3),mask)
            expected=0
            # Independently enumerate the original supported bipartitions.
            for bit,pair in enumerate(((0,1),(0,2),(0,3))):
                if not mask & (1<<bit):continue
                side=set(pair);newside={i for i,x in enumerate(perm) if x in side}
                for nb,np in enumerate(({0,1},{0,2},{0,3})):
                    if newside==np or newside==set(range(4))-np:expected |= 1<<nb
            assert obtained==expected,(perm,mask,obtained,expected)
            count+=1
    return count


def checked_recovery(ss,labels,oracle=None,reference=True):
    n=len(labels); actual_calls=[]
    if oracle is None:oracle=lambda q:quartet_mask(ss,q)
    def measured(q):actual_calls.append(q);return oracle(q)
    result=recover_all(labels,measured)
    assert len(actual_calls)==len(set(actual_calls))==result.total_queries
    assert result.total_queries<=math.comb(n,4)
    assert result.expanded_splits()==ss,(labels,result,ss)
    assert common_order(ss,result.order)
    if reference:
        assert set(labels)==set(range(n))
        # Separate, attributed, unchanged cubic reference; no timing/query savings claim for this validation.
        old=reference_provider().learn_order(n,oracle,anchor=labels[0])
        assert old.independent_orientations==result.internal_vertices,(result,old)
        assert common_order(ss,old.order)
    return result


def small():
    rows=[]
    for n in (4,5,6):
        trees=[tree_splits(g,range(n)) for g in binary_trees(n)]
        unions=set(trees)
        if n<=5:
            for t in trees:unions.update(s|t for s in list(unions))
        else:unions.update(a|b for a,b in combinations(trees,2))
        orders=list(circular_orders(range(n))); runs=maximum=0
        for ss in sorted(unions,key=lambda s:repr(sorted(map(sorted,s)))):
            if not any(common_order(ss,c) for c in orders):continue
            for labels in (tuple(range(n)),tuple(reversed(range(n)))):
                r=checked_recovery(ss,labels)
                runs+=1; maximum=max(maximum,r.total_queries)
        rows.append({'n':n,'joint_runs':runs,'max_unique_queries':maximum,'affine_reference_comparisons':runs})
    return rows


def collision():
    # Byte-independent reconstitution of the occurrence representations in inherited ANCHOR-COLLISION.md.
    a=occurrence_union((0,((((1,2),(3,4)),5),6)),(0,0,1,1,2,3,4))
    b=occurrence_union((0,(((1,(2,3)),(4,5)),6)),(0,0,1,2,2,3,4))
    assert b-a==frozenset((frozenset((2,3)),)) and not a-b
    assert all(quartet_mask(a,q)==quartet_mask(b,q) for q in combinations(range(5),4) if 0 in q)
    runs=[]
    for ss in (a,b):
        for labels in permutations(range(5)):
            r=checked_recovery(ss,labels,reference=False)
            runs.append(r.total_queries)
    return {'runs':len(runs),'maximum_queries':max(runs),
            'same_anchored_table':True,'different_split_detected':[2,3],
            'admission':'Inherited admitted level-two occurrence fixtures; no repeat of the original general source validator.'}


def cut_union(graph,copies):
    """Expected support from physical edge cuts and <=2 straddling pairs;
    oracle below independently uses BFS distances, not these splits.
    """
    p=sparse_provider();n=len(copies);out=set();ambiguous_max=0
    for physical in p.edge_tip_sides(graph,sum(map(len,copies))):
        fixed={i for i,tips in enumerate(copies) if all(t in physical for t in tips)}
        variable=[i for i,tips in enumerate(copies) if any(t in physical for t in tips) and not all(t in physical for t in tips)]
        assert len(variable)<=2;ambiguous_max=max(ambiguous_max,len(variable))
        for flags in product((0,1),repeat=len(variable)):
            a=frozenset(fixed|{i for i,b in zip(variable,flags) if b});b=frozenset(set(range(n))-a)
            if min(len(a),len(b))>=2:out.add(min(a,b,key=lambda s:(len(s),tuple(sorted(s)))))
    return frozenset(out),ambiguous_max


def larger():
    rng=random.Random(202609301156);rows=[]
    p=sparse_provider()
    for n in (8,16,32,64,128,256):
        for kind in ('balanced_tree','caterpillar_tree','random_tree','all_duplicated','mixed_duplicates'):
            counts=[2 if kind=='all_duplicated' else 1+rng.randrange(2) if kind=='mixed_duplicates' else 1 for _ in range(n)]
            copies=[];t=0
            for c in counts:copies.append(list(range(t,t+c)));t+=c
            def balanced(ls):
                if len(ls)==1:return ls[0]
                m=len(ls)//2;return balanced(ls[:m]),balanced(ls[m:])
            leaves=tuple(range(1,t))
            if kind=='balanced_tree':shape=balanced(leaves)
            elif kind=='caterpillar_tree':
                shape=leaves[-1]
                for leaf in reversed(leaves[:-1]):shape=(leaf,shape)
            else:shape=random_shape(leaves,rng)
            graph=p.graph_from_shape(shape,t);ss,amb=cut_union(graph,copies)
            oracle=p.physical_quartet_oracle(graph,copies)
            labels=list(range(n));rng.shuffle(labels)
            r=checked_recovery(ss,tuple(labels),oracle,reference=n<=32)
            if n<=8:
                expected={frozenset(range(i+1,j+1)) for i,j in p.selected_tree_split_union(graph,copies)}
                expected=restrict_splits(expected,range(n));assert expected==ss
            assert len(ss)<=11*n-23
            rows.append({'n':n,'kind':kind,'duplicate_labels':sum(c==2 for c in counts),'k':len(ss),
                         'order_queries':r.order_queries,'joint_unique_queries':r.total_queries,
                         'additional_split_queries':r.total_queries-r.order_queries,
                         'internal_vertices':r.internal_vertices,'retired_vertices':r.retired_vertices,
                         'max_straddling_duplicate_pairs':amb,'reference_compared':n<=32})
    return rows

if __name__=='__main__':
    report={'status':'PASS','python':platform.python_version(),'timestamp_utc':datetime.now(timezone.utc).isoformat(),
            'sparse_git_blob':SPARSE_BLOB,'affine_reference_git_blob':REFERENCE_BLOB,
            'relabel_cases':relabel_tests(),'small_families':small(),'anchor_collision':collision(),'larger':larger(),
            'limits':'Author execution, not independent reviewer execution or a proof of all-size complexity. Larger occurrence controls are graph-derived tree families, not a full admitted-source graph census. Reference audit queries are not included in learner counts. No biological data.'}
    text=json.dumps(report,indent=2)+'\n';Path(__file__).with_name('JOINT-CHECKS.json').write_text(text);print(text)
