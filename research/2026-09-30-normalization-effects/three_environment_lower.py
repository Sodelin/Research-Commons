"""Exact actual-source lower witness for three partial-control environments.

Source embedding is the paired-tip tree written in REPORT.md. This script
checks binary DAG/root-LSA, every switched tree/split, the twelve exact
two-coordinate target events, and every two-row partial-control menu at g=1/2.
It does not substitute synthetic pair coverage for actual displayed targets.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
import json
from pathlib import Path

SHAPE = (((11, 0), (1, 6)), (((7, 2), (3, 8)), ((9, 4), (5, 10))))
TAXA = tuple(range(9))
PAIRS = {i: (6+2*i, 7+2*i) for i in range(3)}


def fixture():
    edges = []
    serial = [0]
    def build(t):
        if isinstance(t, int):
            return 'P'+str(t)
        v = 'V'+str(serial[0]); serial[0] += 1
        for child in t:
            edges.append((v, build(child)))
        return v
    old_root = build(SHAPE)
    neighbours = [b for a,b in edges if a == old_root]
    edges = [(a,b) for a,b in edges if a != old_root]
    edges.append(tuple(neighbours))
    adj = defaultdict(list)
    for a,b in edges:
        adj[a].append(b); adj[b].append(a)
    tip_parent = {i: adj['P'+str(i)][0] for i in range(12)}
    duplicate_tips = {'P'+str(i) for i in range(6,12)}
    base = [(a,b) for a,b in edges if a not in duplicate_tips and b not in duplicate_tips]
    old = next((a,b) for a,b in base if 'P0' in (a,b))
    base.remove(old); base += [('R',old[0]),('R',old[1])]
    adj = defaultdict(list)
    for a,b in base:
        adj[a].append(b); adj[b].append(a)
    directed, seen, todo = [], {'R'}, ['R']
    while todo:
        v=todo.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w); todo.append(w); directed.append((v,w))
    parents = {i: tuple(tip_parent[t] for t in pair) for i,pair in PAIRS.items()}
    fixed = [(('T'+a[1:]) if a.startswith('P') else a,
              ('T'+b[1:]) if b.startswith('P') else b) for a,b in directed]
    fixed += [('H'+str(i),'T'+str(6+i)) for i in range(3)]
    full = fixed + [(p,'H'+str(i)) for i,ps in parents.items() for p in ps]
    vertices={v for edge in full for v in edge}
    preds=defaultdict(list)
    for a,b in full: preds[b].append(a)
    for v in vertices:
        degrees=(len(preds[v]),sum(a==v for a,b in full))
        expected=(0,2) if v=='R' else (1,0) if v.startswith('T') else (2,1) if v.startswith('H') else (1,2)
        assert degrees==expected,(v,degrees)
    done=set(); dominators={}
    while done!=vertices:
        ready={v for v in vertices-done if all(p in done for p in preds[v])}
        assert ready,'Cycle or unreachable node'
        for v in ready:
            dominators[v]=({v} if v=='R' else set.intersection(*(dominators[p] for p in preds[v]))|{v})
        done|=ready
    assert set.intersection(*(dominators['T'+str(i)] for i in TAXA))=={'R'}
    return fixed,parents,full


def switched_splits(fixed,parents,bits):
    edges=fixed+[(parents[i][bits[i]],'H'+str(i)) for i in range(3)]
    adj=defaultdict(list)
    for a,b in edges: adj[a].append(b);adj[b].append(a)
    assert len(edges)==len(adj)-1
    result=set(); full=(1<<9)-1
    for a,b in edges:
        seen={b};todo=[a]
        while todo:
            v=todo.pop()
            if v not in seen: seen.add(v);todo.extend(adj[v])
        mask=sum(1<<i for i in TAXA if 'T'+str(i) in seen)
        if min(mask.bit_count(),9-mask.bit_count())>=2:result.add(min(mask,full^mask))
    assert len(result)==6
    return result


def mass(records,row,probs):
    out=defaultdict(F);total=F(0)
    for bits,splits in records.items():
        if any(c is not None and bits[i]!=c for i,c in enumerate(row)):continue
        w=F(1)
        for i,c in enumerate(row):
            if c is None:w*=probs[i] if bits[i] else 1-probs[i]
        total+=w
        for s in splits:out[s]+=w
    assert total==1
    return out


def main():
    fixed,parents,graph=fixture()
    records={bits:switched_splits(fixed,parents,bits) for bits in product((0,1),repeat=3)}
    support=set().union(*records.values())
    cylinders=[]
    for split in sorted(support):
        event={bits for bits,splits in records.items() if split in splits}
        for i,j in combinations(range(3),2):
            for a,b in product((0,1),repeat=2):
                if event=={bits for bits in records if bits[i]==a and bits[j]==b}:
                    cylinders.append({'split':split,'indices':[i,j],'values':[a,b]})
    assert len(cylinders)==12
    assert {(tuple(c['indices']),tuple(c['values'])) for c in cylinders}=={((i,j),(a,b)) for i,j in combinations(range(3),2) for a,b in product((0,1),repeat=2)}
    rows=list(product((0,None,1),repeat=3))
    covers=[]
    for row in rows:
        m=mass(records,row,[F(1,2)]*3)
        covers.append({s for s in support if m.get(s,F(0))>=F(1,2)})
    two_menus=list(combinations_with_replacement(range(27),2))
    successes=[pair for pair in two_menus if covers[pair[0]]|covers[pair[1]]==support]
    assert not successes
    menu=[(0,0,None),(1,None,None),(None,1,None)]
    comparisons=0
    for g in [F(1,8),F(1,4),F(1,2)]:
        for corner in product((0,1),repeat=3):
            probs=[g if b==0 else 1-g for b in corner]
            ms=[mass(records,row,probs) for row in menu]
            for s in support:
                assert max(m.get(s,F(0)) for m in ms)>=g
                comparisons+=1
    deterministic=[(0,0,0),(0,1,1),(1,0,1),(1,1,0)]
    assert set().union(*(records[row] for row in deterministic))==support
    certain=[{s for s,v in mass(records,row,[F(1,2)]*3).items() if v==1} for row in rows]
    no_three=not any(set().union(*(certain[i] for i in inds))==support for inds in combinations_with_replacement(range(27),3))
    assert no_three
    receipt={'status':'PASS','taxa':9,'hybrids':3,'graph_edges':graph,'hybrid_parents':parents,
        'plane_copy_tree':SHAPE,'cyclic_copy_order':[11,0,1,6,7,2,3,8,9,4,5,10],
        'binary_DAG_LSA_checked':True,'source_embedding_and_galledness':'Paired tips joined in disjoint exterior wedges; every hybrid child is a pendant cut edge. Manual embedding proof in REPORT.md.',
        'switching_trees':8,'nontrivial_split_union_size':len(support),'exact_signed_pair_target_cylinders':cylinders,
        'partial_rows':27,'two_row_menus_checked':len(two_menus),'successful_two_row_menus':len(successes),
        'three_rows':menu,'actual_probability_checks':comparisons,'four_deterministic_rows':deterministic,
        'no_three_partial_environments_give_occurrence_one':no_three,
        'quantifier':'Three is necessary for fixed parameter-oblivious >=g protocols for any 0<g<=1/2; the executed two-row search uses the single fair state g=1/2. Four is necessary for certainty.',
        'not_claimed':['biological experiment','NMSCind partial-control CF bridge','Lean','historical novelty']}
    Path(__file__).with_name('three-environment-lower-checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['status','switching_trees','nontrivial_split_union_size','two_row_menus_checked','successful_two_row_menus','actual_probability_checks','no_three_partial_environments_give_occurrence_one']}))


if __name__=='__main__':main()
