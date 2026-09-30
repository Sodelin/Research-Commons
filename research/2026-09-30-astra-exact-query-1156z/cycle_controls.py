"""Source-admitted long-cycle witnesses saturating the vertex-retirement bound.
Each is an explicit binary rooted level-one network, not an arbitrary family.
"""
from core import edge,tree_splits,quartet_mask,common_order
from insertion_controls import validate_rooted
from recover_all import recover_all,sparse_provider
from pathlib import Path
import json,platform


def cycle_network(n):
    # Cycle vertices n,...,2n-1, hybrid n; root 2n subdivides an ordinary edge.
    if n<4:raise ValueError('Need n>=4.')
    h=n;r=2*n;m=n//2
    directed={(r,n+m),(r,n+m+1),(h,n-1)}
    directed.update((n+i,i-1) for i in range(1,n))
    directed.update((n+i,n+i-1) for i in range(m,0,-1))
    directed.update((n+i,n+i+1) for i in range(m+1,n-1))
    directed.add((2*n-1,h))
    certificate=validate_rooted(directed,set(range(n)),{h})
    # Each switching removes one hybrid-parent edge; degree-two vertices need
    # not be suppressed for BFS quartet topology or physical cut computation.
    trees=[];providers=[];p=sparse_provider()
    for parent in (n+1,2*n-1):
        edges={edge(a,b) for a,b in directed-{(parent,h)}}
        graph={}
        for a,b in edges:graph.setdefault(a,set()).add(b);graph.setdefault(b,set()).add(a)
        trees.append(tree_splits(edges,range(n)))
        providers.append(p.physical_quartet_oracle(graph,[[i] for i in range(n)]))
    union=trees[0]|trees[1]
    def oracle(q):
        value=providers[0](q)|providers[1](q)
        assert value==quartet_mask(union,q)
        return value
    return directed,union,oracle,certificate


def run():
    rows=[]
    for n in (4,5,8,16,32,64,128,256):
        directed,union,oracle,certificate=cycle_network(n)
        result=recover_all(tuple(range(n)),oracle)
        assert result.expanded_splits()==union and common_order(union,result.order)
        assert result.retired_vertices==n-3 and result.internal_vertices==1
        assert len(union)==2*n-6
        rows.append({'n':n,'binary_DAG_LSA':certificate['binary_DAG_LSA'],
                     'rooted_vertices':certificate['vertices'],'rooted_edges':certificate['edges'],
                     'nontrivial_splits':len(union),'retired_vertices':result.retired_vertices,
                     'final_internal_vertices':result.internal_vertices,'order_queries':result.order_queries,
                     'joint_queries':result.total_queries})
    return rows

if __name__=='__main__':
    report={'status':'PASS','python':platform.python_version(),'rows':run(),
            'admission':'For all n>=4, suppressing the root gives a single n-cycle, one pendant taxon per cycle vertex, one hybrid with pendant child. This explicit embedding is outer-labeled planar and galled. The code checks binary degrees, DAG, LSA and both switchings.',
            'limits':'Author controls; no independent review or full graph-class census. The infinite-family structural description is the admission argument, not enumeration.'}
    text=json.dumps(report,separators=(',',':'))+'\n';Path(__file__).with_name('CYCLE-CHECKS.json').write_text(text);print(text)
