"""Exhaustive fixed-label all-transitive color-cube hierarchy audit at m<=5.

Canonical set partitions exhaust all edge colorings up to color names.
The screen includes non-source-realizable affine spaces such as the prime P4.
It checks the hierarchy and color-flip adjacency bound, not a network census.
"""
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
from adaptive_recovery import interval_hierarchy


def partitions(length):
    values=[0]*length
    def visit(i,maximum):
        if i==length:
            yield tuple(values)
            return
        for color in range(maximum+2):
            values[i]=color
            yield from visit(i+1,max(color,maximum))
    yield from visit(1,0)


def run(m):
    labels=tuple(range(m))
    pairs=tuple(combinations(labels,2))
    pi={p:i for i,p in enumerate(pairs)}
    tri_ids=tuple((pi[(a,b)],pi[(a,c)],pi[(b,c)]) for a,b,c in combinations(labels,3))
    checked=valid=assignments=module_intervals=flip_checks=0
    maximum_weight=0
    for part in partitions(len(pairs)):
        checked+=1
        if any(part[ac] not in (part[ab],part[bc]) for ab,ac,bc in tri_ids):
            continue
        valid+=1
        colors=dict(zip(pairs,part))
        weights,nodes=interval_hierarchy(labels,colors)
        maximum_weight=max(maximum_weight,sum(weights.values()))
        assert sum(len(children) for _,children,_ in nodes)<=2*m-2
        assert sum(weights.values())<=4*m-4
        k=max(part)+1
        orders={}
        for bits in product((0,1),repeat=k):
            def before(a,b):
                flip=bits[colors[tuple(sorted((a,b)))]]
                return (not flip) if a<b else bool(flip)
            ranks={a:sum(before(b,a) for b in labels if b!=a) for a in labels}
            order=tuple(sorted(labels,key=lambda a:ranks[a]))
            assert all(before(a,b) for i,a in enumerate(order) for b in order[i+1:])
            orders[bits]=order
            assignments+=1
            positions={a:i for i,a in enumerate(order)}
            for parent,children,palette in nodes:
                assert len(palette)<=2
                for child in children:
                    places=[positions[x] for x in child]
                    assert max(places)-min(places)+1==len(places)
                    module_intervals+=1
        for bits,order in orders.items():
            original={tuple(sorted(p)) for p in zip(order,order[1:])}
            for color in range(k):
                altered=list(bits)
                altered[color]^=1
                target=orders[tuple(altered)]
                following={tuple(sorted(p)) for p in zip(target,target[1:])}
                assert len(following-original)<=2*weights[color]
                flip_checks+=1
    return {"leaves_after_anchor":m,"canonical_edge_partitions":checked,
            "all_transitive_color_cubes":valid,"assignments_checked":assignments,
            "fixed_module_interval_checks":module_intervals,
            "single_color_adjacency_checks":flip_checks,
            "maximum_hierarchy_weight":maximum_weight,"status":"PASS"}


if __name__=='__main__':
    records=[run(m) for m in (3,4,5)]
    report={"status":"PASS","scope":"Every canonical edge-color partition on 3,4,5 ordered leaves whose entire color cube is transitive",
            "records":records,
            "production_sha256":hashlib.sha256(Path(__file__).with_name('adaptive_recovery.py').read_bytes()).hexdigest(),
            "limits":"Finite exact proof controls. No all-size proof, biological validation or optimum claim."}
    Path(__file__).with_name('gallai-audit-controls.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
