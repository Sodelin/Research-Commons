"""Seeded source-realizable partial-support color screens at n=8,16,32.

Trees are independent random binary plane trees sharing a circle. This does
not claim their entire family is the switching family of one admitted network.
Complete support is computed from per-tree rooted triples before queries are
masked; component colors are tested for all-assignment transitivity and induced
monochromatic P4s. Finite tests cannot prove the missing all-size source lemma.
"""
from itertools import combinations
from pathlib import Path
import hashlib
import json
import random


def plane_tree(labels, rng):
    if len(labels) == 1:
        return labels[0]
    cut = rng.randrange(1, len(labels))
    return (plane_tree(labels[:cut], rng), plane_tree(labels[cut:], rng))


def profile(tree, pairs, triples):
    lcas = {}
    serial = 0
    def visit(t):
        nonlocal serial
        if isinstance(t, int):
            return [t]
        left, right = visit(t[0]), visit(t[1])
        serial += 1
        for a in left:
            for b in right:
                lcas[(a,b)] = serial
        return left+right
    visit(tree)
    # Bits relative to ordered quartet r<a<b<c: ra|bc, rc|ab.
    return [1 if lcas[(a,b)] == lcas[(a,c)] else 4 for a,b,c in triples]


def run(n, count, rng):
    labels = tuple(range(1,n))
    pairs = tuple(combinations(labels,2))
    pi = {p:i for i,p in enumerate(pairs)}
    triples = tuple(combinations(labels,3))
    tri_ids = tuple((pi[(a,b)],pi[(a,c)],pi[(b,c)]) for a,b,c in triples)
    quartets = tuple(combinations(labels,4))
    quad_ids = tuple(tuple(pi[p] for p in combinations(q,2)) for q in quartets)
    trees = [plane_tree(labels,rng) for _ in range(96)]
    profiles = [profile(t,pairs,triples) for t in trees]
    all_transitive = p4_checks = arbitrary_tree_failures = 0
    example = None
    for case in range(count):
        family = rng.sample(range(len(trees)),rng.randrange(2,9))
        density = rng.uniform(.25,1)
        masks = []
        for j in range(len(triples)):
            mask = 0
            for k in family:
                mask |= profiles[k][j]
            masks.append(mask if rng.random()<density else 0)
        parent = list(range(len(pairs)))
        def find(x):
            while parent[x]!=x:
                parent[x]=parent[parent[x]]
                x=parent[x]
            return x
        for (ab,ac,bc),mask in zip(tri_ids,masks):
            if mask&1:
                parent[find(ab)]=find(ac)
            if mask&4:
                parent[find(ac)]=find(bc)
        colors = [find(j) for j in range(len(pairs))]
        # These conditions exactly exclude either tournament 3-cycle for each
        # choice of independent color orientation, under the known base circle.
        if any(colors[ac] not in (colors[ab],colors[bc]) or
               colors[ab]==colors[bc]!=colors[ac] for ab,ac,bc in tri_ids):
            continue
        all_transitive += 1
        for q,ids in zip(quartets,quad_ids):
            edge_colors = [colors[j] for j in ids]
            for color in set(edge_colors):
                if edge_colors.count(color)!=3:
                    continue
                degrees = {x:0 for x in q}
                for (a,b),c in zip(combinations(q,2),edge_colors):
                    if c==color:
                        degrees[a]+=1
                        degrees[b]+=1
                p4_checks += 1
                if sorted(degrees.values())==[1,1,2,2]:
                    return {"status":"COUNTEREXAMPLE", "taxa":n,
                            "case":case, "family_trees":[trees[k] for k in family],
                            "triples":triples,"partial_masks":masks,"pair_colors":colors,
                            "P4_taxa":q,"P4_color":color}
        fail = next(((k,j) for k in family for j,((ab,ac,bc),mask) in
                     enumerate(zip(tri_ids,profiles[k])) if
                     ((colors[ab]!=colors[ac]) if mask==1 else (colors[ac]!=colors[bc]))), None)
        if fail is not None:
            arbitrary_tree_failures += 1
            if example is None:
                k,j = fail
                ab,ac,bc = tri_ids[j]
                flip_color = colors[ab] if profiles[k][j]==1 else colors[ac]
                values = [c!=flip_color for c in colors]
                # All-transitive makes predecessor counts distinct valid ranks.
                rank = {x:sum((values[pi[tuple(sorted((x,y)))]] if y<x else
                               not values[pi[(x,y)]]) for y in labels if y!=x)
                        for x in labels}
                order = tuple(sorted(labels,key=lambda x:rank[x]))
                example = {"family_trees":[trees[h] for h in family],
                           "base_order":labels,"queried_support":[[triples[h],m] for h,m in enumerate(masks) if m],
                           "unqueried_or_derived_triplet":triples[j],
                           "tree_triplet_mask":profiles[k][j],
                           "violated_displayed_tree":trees[k],
                           "extra_U0_order":order}
    return {"status":"PASS","taxa":n,"cases":count,
            "all_transitive_partial_spaces":all_transitive,
            "monochromatic_three_edge_graph_checks":p4_checks,
            "spaces_not_contained_in_every_displayed_tree":arbitrary_tree_failures,
            "arbitrary_displayed_tree_failure_example":example}


if __name__ == "__main__":
    rng=random.Random(202609301314)
    records=[]
    for n,count in ((8,20000),(16,5000),(32,1000)):
        record=run(n,count,rng)
        records.append(record)
        print(json.dumps({k:v for k,v in record.items() if k!='arbitrary_displayed_tree_failure_example'}),flush=True)
        if record['status']!='PASS':
            break
    report={"status":"PASS" if all(r['status']=='PASS' for r in records) else "COUNTEREXAMPLE",
            "seed":202609301314,"records":records,
            "limits":"Exact seeded finite screens; arbitrary common-circle tree families need not be one source-admitted network. No all-size proof.",
            "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name('algebra-partial-source-stress.json').write_text(json.dumps(report,indent=2)+'\n')
