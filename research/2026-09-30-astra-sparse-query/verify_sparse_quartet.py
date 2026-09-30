"""Reproducible tests for sparse_quartet.py; no external packages required."""
from __future__ import annotations
import argparse, hashlib, json, platform, random, sys, time
from datetime import datetime, timezone
from itertools import combinations
from math import comb
from pathlib import Path
from sparse_quartet import (candidates, seed_rectangles, recover, query_bound,
    validate_partition, split_support_oracle, shapes, graph_from_shape,
    selected_tree_split_union, physical_quartet_oracle)

HERE=Path(__file__).resolve().parent


def check_result(n, support, oracle, *, require_tree_support=False):
    result=recover(n,oracle,require_tree_support=require_tree_support)
    assert result.splits==frozenset(support),(n,support,result)
    assert result.oracle_calls <= result.rectangle_tests
    assert result.rectangle_tests == 2*n-6+2*result.positive_internal_nodes
    assert result.rectangle_tests <= query_bound(n,len(support))
    return result


def abstract():
    rows=[]
    for n in range(4,8):
        p=candidates(n); total=1<<len(p); max_queries=max_tests=0
        # Precompute each individual split's restriction to every quartet.
        qs=list(combinations(range(n),4))
        contribution=[]
        for s in p:
            o=split_support_oracle(n,[s]); contribution.append([o(q) for q in qs])
        for subset in range(total):
            support=[p[i] for i in range(len(p)) if subset>>i&1]
            masks=[0]*len(qs)
            for i in range(len(p)):
                if subset>>i&1:
                    masks=[a|b for a,b in zip(masks,contribution[i])]
            table=dict(zip(qs,masks))
            r=check_result(n,support,table.__getitem__)
            max_queries=max(max_queries,r.oracle_calls); max_tests=max(max_tests,r.rectangle_tests)
        rows.append(dict(n=n,candidate_splits=len(p),support_families=total,
                         max_unique_queries=max_queries,max_rectangle_tests=max_tests))
    for n in range(4,257): validate_partition(n)
    single_cases=0
    for n in range(4,33):
        for s in candidates(n):
            check_result(n,[s],split_support_oracle(n,[s])); single_cases+=1
    return dict(rows=rows,total_support_families=sum(r['support_families'] for r in rows),
                partition_n_range=[4,256],single_split_localization_cases=single_cases,
                scope='All circular split subsets through n=7, including families not realized by a binary tree union')


def graphs(max_n=5):
    rows=[]
    for n in range(4,max_n+1):
        count=selected_families=queries=0; systems=set(); max_k=0
        for doubled in range(1<<n):
            copies=[]; pos=0
            for label in range(n):
                number=1+((doubled>>label)&1)
                copies.append(list(range(pos,pos+number))); pos+=number
            for shape in shapes(1,pos):
                graph=graph_from_shape(shape,pos)
                support=selected_tree_split_union(graph,copies)
                oracle=physical_quartet_oracle(graph,copies)
                r=check_result(n,support,oracle,require_tree_support=True)
                # Full quartet table checks that recovered splits regenerate every topology.
                split_oracle=split_support_oracle(n,support)
                table=[]
                for q in combinations(range(n),4):
                    value=oracle(q); assert value==split_oracle(q)
                    table.append(value)
                systems.add(tuple(table)); count+=1
                selected_families += 1<<doubled.bit_count()
                queries += r.oracle_calls; max_k=max(max_k,len(support))
        rows.append(dict(n=n,ordered_tree_duplication_instances=count,
                         globally_selected_trees=selected_families,
                         distinct_quartet_systems=len(systems),
                         actual_reconstruction_queries=queries,max_nontrivial_splits=max_k))
    return dict(rows=rows,total_instances=sum(r['ordered_tree_duplication_instances'] for r in rows),
                total_globally_selected_trees=sum(r['globally_selected_trees'] for r in rows),
                scope='Plane occurrence trees with each label once or twice contiguously; no independent raw source-network admission checker')


def stress():
    rng=random.Random(202609300938)
    rows=[]
    for n in [16,32,64,128,256]:
        p=candidates(n)
        scenarios={
            'random_n':set(rng.sample(p,min(n,len(p)))),
            'random_2n':set(rng.sample(p,min(2*n,len(p)))),
            'caterpillar_tree':{(0,j) for j in range(2,n-1)},
            'near_diagonal':{(i,i+2) for i in range(n-2)}|{(1,n-1)},
        }
        if n<=32: scenarios['all_circular_splits']=set(p)
        for kind,support in scenarios.items():
            r=check_result(n,support,split_support_oracle(n,support))
            rows.append(dict(n=n,kind=kind,k=len(support),unique_quartet_queries=r.oracle_calls,
                             rectangle_tests=r.rectangle_tests,bound=query_bound(n,len(support)),
                             all_quartets=comb(n,4),all_nontrivial_boundary_candidates=len(p)))
    # Deliberately corrupt one answer on a real quartet tree.
    o=split_support_oracle(4,[(0,2)])
    correct=recover(4,o)
    incorrect=recover(4,lambda q:1)
    assert correct.splits != incorrect.splits
    controls=0
    for n, oracle in [(3,lambda q:1),(4,lambda q:2),(4,lambda q:0),(4,lambda q:8)]:
        try: recover(n,oracle)
        except ValueError: controls+=1
        else: raise AssertionError('invalid-input control failed')
    return dict(seed=202609300938,rows=rows,
                invalid_input_controls_passed=controls,
                deliberately_wrong_valid_oracle_changes_output=True,
                scope='Synthetic geometric support families; query counts are not biological speed benchmarks')


def main():
    if not __debug__: raise RuntimeError('Do not run with -O')
    parser=argparse.ArgumentParser();parser.add_argument('phase',choices=['abstract','graphs','stress'])
    parser.add_argument('--max-n',type=int,default=5); args=parser.parse_args()
    started=time.perf_counter()
    result=graphs(args.max_n) if args.phase=='graphs' else globals()[args.phase]()
    receipt=dict(status='PASS',phase=args.phase,created_utc=datetime.now(timezone.utc).isoformat(),
                 python=sys.version,platform=platform.platform(),elapsed_seconds=time.perf_counter()-started,
                 sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in [HERE/'sparse_quartet.py',Path(__file__).resolve()]},result=result)
    path=HERE/f'verification-{args.phase}.json';path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__': main()
