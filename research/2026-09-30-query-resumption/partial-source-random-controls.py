"""Seeded valid binary-tree-family screen for the partial containing-tree lemma.

Pair-color transitivity and the symbolic-ultrametric P4 obstruction are checked.
This tests an all-size conjecture; a pass is not a proof. No source-network
realization is asserted for any arbitrary tree-family counterexample.
"""
from itertools import combinations
from pathlib import Path
import importlib.util
import json
import random

BASE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("graph_truth", BASE.parent / "2026-09-30-root-exact-query" / "verify_candidate_order.py")
truth = importlib.util.module_from_spec(spec)
spec.loader.exec_module(truth)


def run(n=7, trials=100000, seed=20260930):
    rng = random.Random(seed)
    Y = tuple(range(1, n))
    pairs = tuple(combinations(Y, 2))
    pidx = {p: i for i, p in enumerate(pairs)}
    triples = tuple(combinations(Y, 3))
    triangle_indices = [(pidx[(a,b)], pidx[(a,c)], pidx[(b,c)]) for a,b,c in triples]
    profiles, graphs, splits = [], [], []
    for G in truth.trees(n):
        S = truth.graph_splits(G, n)
        if not all(truth.is_circular(s, tuple(range(n))) for s in S):
            continue
        profile = []
        for a,b,c in triples:
            Q=(0,a,b,c)
            vals = {truth.topology_bit(Q, [x for x in Q if s & (1<<x)],0)
                    for s in S if sum(bool(s&(1<<x)) for x in Q)==2}
            assert len(vals)==1
            val=vals.pop()
            assert val in (1,4)
            profile.append(val)
        profiles.append(profile);graphs.append(G);splits.append(S)
    quartets=[]
    for V in combinations(Y,4):
        Es=tuple(combinations(V,2)); idx=tuple(pidx[e] for e in Es)
        quartets.append((V,Es,idx))
    allcyclic=0
    for t in range(trials):
        size=rng.choice((1,2,2,2,3,3,4,8,min(len(profiles),16)))
        fam=rng.sample(range(len(profiles)),size)
        profile=[0]*len(triples)
        for j in fam:
            for i,v in enumerate(profiles[j]):profile[i]|=v
        chosen=[i for i in range(len(triples)) if rng.random()<rng.choice((.2,.4,.6,.8))]
        parent=list(range(len(pairs)))
        def find(i):
            while parent[i]!=i:
                parent[i]=parent[parent[i]];i=parent[i]
            return i
        def join(i,j):
            parent[find(i)]=find(j)
        for i in chosen:
            a,b,c=triangle_indices[i];mask=profile[i]
            if mask&1:join(a,b)
            if mask&4:join(b,c)
        color=[find(i) for i in range(len(pairs))]
        if not all(color[b] in (color[a],color[c]) for a,b,c in triangle_indices):
            continue
        allcyclic+=1
        for V,Es,idx in quartets:
            labels=[color[i] for i in idx]
            for label in set(labels):
                chosenE=[E for E,l in zip(Es,labels) if l==label]
                if len(chosenE)!=3:continue
                deg={v:0 for v in V}
                for a,b in chosenE:deg[a]+=1;deg[b]+=1
                if sorted(deg.values())==[1,1,2,2]:
                    return {"status":"COUNTEREXAMPLE","taxa":n,"seed":seed,
                            "trials_before_witness":t+1,"all_cyclic_partial_systems":allcyclic,
                            "family_indices":fam,"family_graphs":[sorted(graphs[j]) for j in fam],
                            "family_splits":[sorted(splits[j]) for j in fam],
                            "queried_triples":[triples[i] for i in chosen],
                            "queried_masks":[profile[i] for i in chosen],
                            "pair_colors":list(zip(pairs,color)),
                            "induced_P4_taxa":V,"induced_P4_edges":chosenE}
    return {"status":"PASS","taxa":n,"seed":seed,"trials":trials,
            "canonical_compatible_trees":len(profiles),
            "all_cyclic_partial_systems":allcyclic,
            "claim":"No containing-tree obstruction found; finite screen only"}


if __name__=="__main__":
    result=run()
    (BASE/"partial-source-random-controls.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
