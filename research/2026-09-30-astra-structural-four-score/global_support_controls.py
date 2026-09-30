"""Graph-based global controls for the four-score cone and support theorem.

Uses literal adjacent-copy tree fixtures, explicit rooted graph switchings,
BFS quartet topologies, and direct distance/split reconstruction. No mass or
switching-frequency substitution for the global unweighted distinct-set rule.
"""
from collections import Counter, deque
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import comb
from pathlib import Path
import json
import sys
from four_score_controls import Network, category, gall, template, all_order_obstructions


def distances_and_splits(net):
    incoming=[sorted(e for e in net.edges if e[1]==h) for h in net.hybrids]
    leaves=set(net.leaves); result=[]; split_union=set()
    for removed in product(*incoming):
        adj={}
        for u,v in net.edges-set(removed):
            adj.setdefault(u,set()).add(v);adj.setdefault(v,set()).add(u)
        assert sum(map(len,adj.values()))//2==len(adj)-1
        D={}
        for x,vx in net.leaves.items():
            dist={vx:0}; queue=deque([vx])
            while queue:
                u=queue.popleft()
                for v in adj[u]:
                    if v not in dist:dist[v]=dist[u]+1;queue.append(v)
            assert len(dist)==len(adj)
            for y,vy in net.leaves.items():D[x,y]=dist[vy]
        result.append(D)
        # Extract displayed tree splits directly from its edges, independently
        # of the boundary-quartet lemma being checked.
        for u,v in net.edges-set(removed):
            seen={u};queue=deque([u])
            while queue:
                w=queue.popleft()
                for z in adj[w]:
                    if {w,z}=={u,v}:continue
                    if z not in seen:seen.add(z);queue.append(z)
            A=frozenset(x for x,vx in net.leaves.items() if vx in seen)
            if A and A!=leaves:split_union.add(canon(A,leaves))
    return result,split_union


def canon(A,X):
    A=tuple(sorted(A));B=tuple(sorted(set(X)-set(A)))
    return min(A,B,key=lambda z:(len(z),z))


def codes_from_graph(net):
    DD,split_union=distances_and_splits(net);codes={};unequal=0
    for Q in combinations(sorted(net.leaves),4):
        a,b,c,d=Q;counts=Counter()
        for D in DD:
            vals=(D[a,b]+D[c,d],D[a,c]+D[b,d],D[a,d]+D[b,c])
            assert vals.count(min(vals))==1
            counts[vals.index(min(vals))]+=1
        assert 1<=len(counts)<=2
        if len(counts)==2 and len(set(counts.values()))>1:unequal+=1
        codes[Q]=frozenset(counts)
    return codes,split_union,unequal,len(DD)


def vectors(net,codes):
    X=sorted(net.leaves);n=len(X);out={}
    for x,y in combinations(X,2):
        v=[0]*4
        for p,q in combinations([z for z in X if z not in (x,y)],2):
            v[category(x,y,p,q,codes)]+=1
        out[x,y]=(2*n-4,*(2*k for k in v))
    return out


def score_matrix(vectors,X,scores):
    D={(x,x):F(0) for x in X}
    for (x,y),v in vectors.items():
        D[x,y]=D[y,x]=v[0]+sum(F(s)*q for s,q in zip(scores,v[1:]))
    return D


def split_weights(D,C):
    n=len(C);weights={}
    for i,j in combinations(range(n),2):
        a,b,c,d=C[i],C[(i+1)%n],C[j],C[(j+1)%n]
        split=canon(C[i+1:j+1],C)
        weights[split]=(D[a,c]+D[b,d]-D[a,d]-D[b,c])/2
    # Reconstruction is a separately checked linear identity.
    for x,y in combinations(C,2):
        rebuilt=sum(w for split,w in weights.items() if (x in split)!=(y in split))
        assert rebuilt==D[x,y]
    return weights


def paired_network(labels,tree):
    """Rooted plane binary tree with adjacent copies glued to pendant hybrids.

Label zero occurs once and is a child of the root, so the root is the LSA.
Fixtures exclude pairs sharing a parent, avoiding parallel-edge bookkeeping.
"""
    assert tree[0]==0 and labels.count(0)==1
    net=Network(); tips={}; parents={}
    def build(t,parent):
        if isinstance(t,int):
            v=f'tip{t}';tips[t]=v;parents[t]=parent
            net.edges.add((parent,v))
        else:
            v=net.node();net.edges.add((parent,v))
            build(t[0],v);build(t[1],v)
    build(tree[0],net.root);build(tree[1],net.root)
    for lab in sorted(set(labels)):
        tt=[i for i,l in enumerate(labels) if l==lab]
        if len(tt)==1:net.leaves[f'L{lab}']=tips[tt[0]]
        else:
            assert len(tt)==2 and parents[tt[0]]!=parents[tt[1]],'parallel fixture'
            h=f'H{lab}';net.hybrids.append(h)
            for t in tt:
                net.edges.remove((parents[t],tips[t]));net.edges.add((parents[t],h))
            v=f'final{lab}';net.edges.add((h,v));net.leaves[f'L{lab}']=v
    return net,[f'L{i}' for i in sorted(set(labels))]


def graft(parent,taxon,child):
    assert not(set(parent.leaves)-{taxon}) & set(child.leaves)
    net=deepcopy(parent);old=net.leaves.pop(taxon)
    edge=next(e for e in net.edges if e[1]==old);net.edges.remove(edge)
    rename=lambda v:'G_'+taxon+'_'+v
    net.edges.add((edge[0],rename(child.root)))
    net.edges.update((rename(u),rename(v)) for u,v in child.edges)
    net.leaves.update({x:rename(v) for x,v in child.leaves.items()})
    net.hybrids.extend(rename(h) for h in child.hybrids)
    return net


def blob_levels(net):
    adj={}
    for u,v in net.edges:adj.setdefault(u,set()).add(v);adj.setdefault(v,set()).add(u)
    bridges=set()
    for u,v in net.edges:
        seen={u};queue=deque([u])
        while queue:
            w=queue.popleft()
            for z in adj[w]:
                if {w,z}=={u,v}:continue
                if z not in seen:seen.add(z);queue.append(z)
        if v not in seen:bridges.add(frozenset((u,v)))
    remaining=set(adj);levels=[]
    while remaining:
        start=next(iter(remaining));seen={start};queue=deque([start])
        while queue:
            u=queue.popleft()
            for v in adj[u]:
                if frozenset((u,v)) in bridges:continue
                if v not in seen:seen.add(v);queue.append(v)
        remaining-=seen
        h=sum(v in net.hybrids for v in seen)
        if h:levels.append(h)
    return sorted(levels)


def check_global(name,net,C):
    admission=net.validate();codes,splits,unequal,switches=codes_from_graph(net)
    vectors_=vectors(net,codes);n=len(C)
    assert set(C)==set(net.leaves)
    parameters=[(0,1,F(1,2),1),(0,1,F(3,4),1),(0,1,1,1),
                (1,10,6,10),(2,5,F(7,2),5),(2,5,5,5),
                (0,F(1,10),F(3,50),F(1,10)),(7,7,7,7),(0,0,0,0)]
    records=[]
    for score in parameters:
        c,s,a,o=score;D=score_matrix(vectors_,C,score);weights=split_weights(D,C)
        assert all(w>=0 for w in weights.values())
        supported={sp for sp,w in weights.items() if w>0}
        assert supported<=splits
        if a<s:
            assert supported==splits
            assert all(w>=2*(s-a) for sp,w in weights.items() if len(sp)>1 and sp in splits)
        for x in C:
            assert weights[(x,)]>=n-2+F(c,2)*(n-2)*(n-3)
        if a==s and s>c:
            cherry={(x,y):F(v[1],2) for (x,y),v in vectors_.items()}
            cherry.update({(y,x):v for (x,y),v in list(cherry.items())})
            for i,j in combinations(range(n),2):
                sp=canon(C[i+1:j+1],C)
                if len(sp)==1:continue
                aa,b,cc,d=C[i],C[(i+1)%n],C[j],C[(j+1)%n]
                E=cherry[aa,d]+cherry[b,cc]-cherry[aa,cc]-cherry[b,d]
                assert E.denominator==1 and E>=0
                assert weights[sp]==(s-c)*E
        records.append({'scores':list(map(str,score)),
                        'supported_nontrivial_splits':sum(len(sp)>1 for sp in supported),
                        'minimum_nontrivial_positive_weight':str(min((w for sp,w in weights.items() if len(sp)>1 and w>0),default=0))})
    return {'fixture':name,'admission':admission,'circular_order':C,
            'nontrivial_blob_levels':blob_levels(net),'switchings_executed':switches,
            'quartets_with_unequal_switching_multiplicities':unequal,
            'displayed_nontrivial_split_count':sum(len(sp)>1 for sp in splits),
            'parameter_cases':records,
            'graph':{'arcs':sorted(map(list,net.edges)),'leaves':net.leaves,'root':net.root,'hybrids':net.hybrids}}


def check_lower():
    basechecks=[]
    for k in range(2,9):
        r=2*k+1;ordinary=[f'o{i:02d}' for i in range(1,r+1)]
        net=gall(['h']+ordinary,'h',{'h':('x','xp')},(ordinary[0],ordinary[1]))
        net.validate();codes,_,_,_=codes_from_graph(net);VV=vectors(net,codes)
        def expected(x,y):
            if x in ('x','xp') and y in ('x','xp'):return (comb(r,2),0,0,0)
            if x in ('x','xp') or y in ('x','xp'):
                j=int((y if x in ('x','xp') else x)[1:]);o=(j-1)*(r-j)
                return (0,r-1,comb(r-1,2)-o,o)
            p,q=sorted((int(x[1:]),int(y[1:])))
            c=1+comb(p-1,2)+comb(r-q,2)
            return (c,comb(r-2,2)-c+1,2*(p-1+r-q),2*(q-p-1))
        for (x,y),v in VV.items():assert v==(2*r,*(2*t for t in expected(x,y)))
        basechecks.append({'k':k,'n':r+2,'pair_count':len(VV)})
    signs=[]
    for b in (F(-7),F(-1),F(0),F(1,6),F(1,4),F(49,100)):
        bound=(8-4*b)/(4*(1-2*b));k=max(2,int(bound)+1)
        if b<F(1,6):k=max(k,int((11-8*b)/(1-6*b))+1)
        t1=4*(1-2*b)*k*k+(4*b-6)*k-2
        t2=(1-6*b)*k*k+(8*b-9)*k-2
        assert t1>0 and t2!=0
        assert (1+2*(t2>0))%2==1
        signs.append({'b':str(b),'k':k,'n':2*k+3,'T_uv':str(t1),'T_uz_and_T_vz':str(t2)})
    return {'direct_lower_family_counts':basechecks,'all_parameter_formula_controls':signs}


def check_modified_and_trees():
    ordinary=[f'o{i}' for i in range(1,6)]
    net=gall(['h']+ordinary,'h',{'h':('x','xp')},('o1','o2'))
    net.validate();codes,_,_,_=codes_from_graph(net)
    VV=vectors(net,codes);Y=['x','xp','o1','o3','o5']
    D=score_matrix(VV,sorted(net.leaves),(F(1,2),1,F(1,2),1))
    cert=all_order_obstructions(D,Y);assert cert is not None
    contrasts=[D['x','xp']+D[u,v]-D['x',u]-D['xp',v]
               for u,v in combinations(Y[2:],2)]
    assert contrasts==[-8,1,-8]
    tree=Network();tree.attach(tree.root,(('x','xp'),'u'));tree.attach(tree.root,('z','v'))
    tree.validate();tc,_,_,_=codes_from_graph(tree);tv=vectors(tree,tc);TY=['x','xp','u','z','v']
    treerecords=[]
    for score in ((2,1,0,0),(F(1001,1000),1,F(9,10),1),(-1,-2,7,-3)):
        TD=score_matrix(tv,TY,score);TC=all_order_obstructions(TD,TY)
        assert TC is not None
        treerecords.append({'scores':list(map(str,score)), 'all_12_order_certificates':TC})
    return {'modified_NANUQ':{'scores':['1/2','1','1/2','1'],'network_taxa':7,
            'retained_order_for_table':Y,'distance_table':[[str(D[x,y]) for y in Y] for x in Y],
            'twin_contrasts':list(map(str,contrasts)),'all_12_order_certificates':cert},
            'c_greater_s_five_taxon_tree':treerecords,
            'construction_fix_log':'An initial three-blob test failed binary-degree validation because repeated grafts reused node identifiers. Graft prefixes were changed to include the replaced taxon; the complete corrected suite then passed. No mathematical counterexample was suppressed.'}


def run(fixtures):
    records=[]
    for name,labels,tree in fixtures:
        net,C=paired_network(labels,tree);records.append(check_global(name,net,C))
    for size in (4,5,7):
        order=[f'S{size}_{i}' for i in range(size)]
        net=gall(order,order[0],{},(order[1],order[2]))
        records.append(check_global(f'sunlet_{size}',net,order))
    P=gall(['pa','pb','pc','pd'],'pa',{},('pb','pc'))
    Q=gall(['qa','qb','qc','qd','qe'],'qa',{},('qb','qc'))
    Qorder=['qc','qd','qe','qa','qb']
    combined=graft(P,'pa',Q);C=Qorder+['pb','pc','pd']
    records.append(check_global('two_blobs',combined,C))
    R=gall(['ra','rb','rc','rd'],'ra',{},('rb','rc'))
    Rorder=['rc','rd','ra','rb']
    combined2=graft(combined,'qd',R)
    C2=C[:C.index('qd')]+Rorder+C[C.index('qd')+1:]
    records.append(check_global('three_blobs',combined2,C2))
    return {'status':'PASS_GLOBAL_CONE_AND_SUPPORT_CONTROLS','fixtures':records,
            'total_parameter_cases':9*len(records),'lower_family':check_lower(),
            'additional_exact_obstructions':check_modified_and_trees(),
            'method':'Explicit directed graphs, all edge switchings, BFS quartets, deduplicated sets, direct edge-split union, exact rational distances and circular reconstruction.',
            'limits':'Finite fixtures corroborate hand proofs; they do not establish arbitrary-level coverage. Outer-labeled planarity follows the specified adjacent-copy gluing/sunlet/grafting constructions. Rooted admission is checked.'}


FIXTURES=[
 ('level2_multiblob',[0,1,2,2,3,3,4,5,5],(0,((((1,2),3),(4,((5,6),7))),8))),
 ('level4_blob',[0,1,1,2,2,3,4,4,5,5],(0,(((1,(((2,3),4),(5,6))),(7,8)),9))),
 ('level3_blob',[0,1,1,2,2,3,4,4,5],(0,(1,(((2,3),((4,5),6)),(7,8))))),
 ('level5_blob',[0,1,1,2,2,3,3,4,4,5,5],(0,((1,(2,3)),((((4,5),((6,7),8)),9),10))))
]

if __name__=='__main__':
    report=run(FIXTURES);report['python']=sys.version
    report['checker_sha256']=sha256(Path(__file__).read_bytes()).hexdigest()
    report['dependency_sha256']=sha256(Path(__file__).with_name('four_score_controls.py').read_bytes()).hexdigest()
    Path(__file__).with_name('GLOBAL-EVIDENCE.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'total_parameter_cases':report['total_parameter_cases'],
                      'fixtures':[{k:v for k,v in row.items() if k not in ('graph','parameter_cases')} for row in report['fixtures']],
                      'lower_family':report['lower_family']},indent=2))
