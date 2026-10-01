#!/usr/bin/env python3
"""Exact finite controls for G7-MAXIMAL-20261001; not an all-source QE engine.

Run: python checks.py --output checks.json
Only the Python standard library is required. All correctness assertions use
integers or Fraction. Floating-point optimization is not used in this replay.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools as it
import json
from fractions import Fraction as F
from pathlib import Path


def mask_rows(r: int) -> list[tuple[int, ...]]:
    return list(it.product((0, 1), repeat=r))


def pair_cells(r: int) -> list[tuple[int, int, int, int]]:
    return [(i, j, a, b) for i, j in it.combinations(range(r), 2)
            for a, b in it.product((0, 1), repeat=2)]


def margins(rows: list[tuple[int, ...]], weights: list[F]) -> list[F]:
    assert rows and len(rows) == len(weights) and sum(weights) == 1
    return [sum((w for x, w in zip(rows, weights) if (x[i], x[j]) == (a, b)), F(0))
            for i, j, a, b in pair_cells(len(rows[0]))]


def sylvester_design(r: int) -> list[tuple[int, ...]]:
    assert r >= 2
    d = r.bit_length()  # ceil(log2(r+1))
    return [tuple((u & v).bit_count() % 2 for v in range(1, r + 1))
            for u in range(1 << d)]


def five_row_certificate() -> dict:
    rows = mask_rows(4)
    cells = pair_cells(4)
    counts: dict[str, int] = {}
    covers = []
    for d in range(1, 6):
        number = 0
        for support in it.combinations(range(16), d):
            witnesses = [[j for j, idx in enumerate(support)
                          if (rows[idx][i], rows[idx][k]) == (a, b)]
                         for i, k, a, b in cells]
            if any(not w for w in witnesses):
                continue
            number += 1
            assert d == 5  # smaller supports cannot cover all pair assignments
            # One singleton event for EACH atom gives w_j >= rho, hence 5 rho <= 1.
            singleton_atoms = {w[0] for w in witnesses if len(w) == 1}
            assert singleton_atoms == set(range(5))
            assert min(margins([rows[i] for i in support], [F(1, 5)] * 5)) == F(1, 5)
            covers.append(support)
        counts[str(d)] = number
    assert counts == {'1': 0, '2': 0, '3': 0, '4': 0, '5': 16}
    payload = json.dumps(covers, separators=(',', ':')).encode()
    return {'subsets_examined': sum(__import__('math').comb(16, d) for d in range(1, 6)),
            'covering_support_counts': counts, 'all_five_atom_singleton_duals_pass': True,
            'optimal_margin_at_most_five_configurations': '1/5',
            'covering_support_sha256': hashlib.sha256(payload).hexdigest(),
            'example': [list(rows[i]) for i in covers[0]]}


def graph(kind: str, r: int, active: int) -> tuple[list[tuple[str, str]], dict[str, list[tuple[str, str]]]]:
    assert r >= 1 and 0 <= active < r
    if kind == 'triangle':
        arcs = [('R','D'),('R','U'),('U','V'),('U','H'),('V','C'),('V','H'),('H','W'),('W','A'),('W','B')]
        pendant = ('R','D')
    elif kind == 'diamond':
        arcs = [('R','B'),('R','U'),('U','V'),('U','W'),('V','C'),('V','H'),('W','D'),('W','H'),('H','A')]
        pendant = ('R','B')
    else:
        raise ValueError(kind)
    controls = {f'h{active}': [e for e in arcs if e[1] == 'H']}
    if r > 1:
        arcs.remove(pendant)
        parent, tip = pendant
        for j in (j for j in range(r) if j != active):
            p, h = f'P{j}', f'J{j}'
            arcs += [(parent,p),(p,h),(p,h)]
            controls[f'h{j}'] = [(p,h),(p,h)]
            parent = h
        arcs.append((parent,tip))
    return arcs, controls


def reachable(start: str, adj: dict[str, set[str]]) -> set[str]:
    seen = {start}; stack = [start]
    while stack:
        for y in adj[stack.pop()]:
            if y not in seen:
                seen.add(y); stack.append(y)
    return seen


def check_admission_basics(arcs: list[tuple[str,str]], r: int) -> None:
    vs = {x for e in arcs for x in e}
    inc = {v: 0 for v in vs}; out = dict(inc)
    adj = {v:set() for v in vs}
    for a,b in arcs:
        inc[b] += 1; out[a] += 1; adj[a].add(b)
    assert len(vs) == 2*4 + 2*r - 1 and len(arcs) == 2*4 + 3*r - 2
    assert (inc['R'], out['R']) == (0,2)
    assert all((inc[t], out[t]) == (1,0) for t in 'ABCD')
    assert all((inc[v],out[v]) in {(1,2),(2,1)} for v in vs - set('ABCDR'))
    assert sum(inc[v] == 2 for v in vs) == r
    assert reachable('R',adj) == vs
    # Kahn with parallel arcs counted, and source root stable-ancestor check.
    deg = inc.copy(); queue=[v for v in vs if deg[v] == 0]; order=[]
    while queue:
        v=queue.pop(); order.append(v)
        for a,b in arcs:
            if a == v:
                deg[b]-=1
                if deg[b] == 0: queue.append(b)
    assert len(order) == len(vs)
    dom={}
    for v in order:
        parents={a for a,b in arcs if b==v}
        dom[v] = {v} if not parents else {v} | set.intersection(*(dom[a] for a in parents))
    assert set.intersection(*(dom[t] for t in 'ABCD')) == {'R'}
    for h in (v for v in vs if inc[v] == 2):
        edge=next(e for e in arcs if e[0]==h)
        remaining=arcs.copy(); remaining.remove(edge)
        und={v:set() for v in vs}
        for a,b in remaining: und[a].add(b);und[b].add(a)
        assert edge[1] not in reachable(edge[0],und)


def displayed_splits(arcs: list[tuple[str,str]], controls: dict[str,list[tuple[str,str]]]) -> set[str]:
    answer=set(); keys=sorted(controls)
    for bits in it.product((0,1),repeat=len(keys)):
        selected=arcs.copy()
        for key,bit in zip(keys,bits): selected.remove(controls[key][1-bit])
        vs={v for e in selected for v in e}
        und={v:set() for v in vs}
        for a,b in selected:und[a].add(b);und[b].add(a)
        for a,b in selected:
            und[a].remove(b);und[b].remove(a)
            left=set('ABCD') & reachable(a,und)
            und[a].add(b);und[b].add(a)
            if len(left)==2:
                sides=sorted([''.join(sorted(left)), ''.join(sorted(set('ABCD')-left))])
                answer.add('|'.join(sides))
    return answer


def collision_and_padding() -> dict:
    x=u=v=F(9,10); w=F(1,10); gamma=F(1,2)
    a=1-x+x*(gamma**2*(1-2*u/3)+(1-gamma)**2*(1-2*v/3)+2*gamma*(1-gamma)*w/3)
    pT=(a,(1-a)/2,(1-a)/2)
    z=F(177,200)
    pD=(z/3,(1-z/3)/2,(1-z/3)/2)
    assert pT==pD==(F(59,200),F(141,400),F(141,400))
    forced=(1-2*x*u/3,x*u/3,x*u/3)
    assert forced==(F(23,50),F(27,100),F(27,100))
    graphs=0; switches=0
    for r in range(1,7):
        for active in range(r):
            for kind,target in [('triangle',{'AB|CD'}),('diamond',{'AC|BD','AD|BC'})]:
                arcs,controls=graph(kind,r,active)
                check_admission_basics(arcs,r)
                assert displayed_splits(arcs,controls)==target
                graphs+=1;switches+=2**r
    return {'exact_shared_untouched_law':[str(x) for x in pT],
            'triangle_active_endpoint_law':[str(x) for x in forced],
            'padded_graphs_checked':graphs,'switchings_checked':switches,
            'r_tested':[1,2,3,4,5,6],
            'checks':['binary degree','complete reachability','acyclicity','LSA root','hybrid child bridges','displayed quartet union'],
            'not_computed':'General planarity certification and all-source biological law enumeration; the embedding and padding proof is in the manuscript.'}


def confidence_integer(s: int, coordinates: int, delta: F) -> int:
    assert s>=1 and coordinates>=1 and 0<delta<1
    target=F(2*coordinates*s*(s+1),1)/delta
    k=0
    while (1 << k) < target:k+=1
    return k


def certified_winner(counts: tuple[int,int,int], s: int, k: int) -> int | None:
    assert sum(counts)==s
    ranking=sorted(range(3),key=lambda i:counts[i],reverse=True)
    gap=counts[ranking[0]]-counts[ranking[1]]
    return ranking[0] if gap>0 and gap*gap>2*k*s else None


def exact_statistical_controls() -> dict:
    delta=F(1,20); d=15; trials=0
    for s in [1,2,10,100,1000,10000,100000]:
        k=confidence_integer(s,d,delta)
        assert F(2,1<<k)<=delta/F(d*s*(s+1))
        trials+=1
    for n in range(1,101):
        assert sum((F(1,s*(s+1)) for s in range(1,n+1)),F(0))==1-F(1,n+1)
    # Deterministic count fixtures test the certificate, NOT a coverage simulation.
    fixtures=[]
    for index in range(3):
        s=30000; counts=[9000]*3;counts[index]=12000
        k=confidence_integer(s,d,delta)
        assert certified_winner(tuple(counts),s,k)==index
        fixtures.append({'s':s,'counts':counts,'k':k,'winner':index})
    assert certified_winner((10000,10000,10000),30000,confidence_integer(30000,d,delta)) is None
    for denominator in range(2,102):
        z=F(denominator-1,denominator)
        p=(1-2*z/3,z/3,z/3);q=(z/3,1-2*z/3,z/3)
        assert sum(abs(a-b) for a,b in zip(p,q))/2 == 1-z
        assert max(p)-min(p)==1-z
    for denominator in range(2,102):
        epsilon=F(1,denominator)
        row0=(F(2,3),F(1,6),F(1,6))
        row1=((1-epsilon)/3,(1+2*epsilon)/3,(1-epsilon)/3)
        pooled=tuple((a+b)/2 for a,b in zip(row0,row1))
        expected=(F(1,2)-epsilon/6,F(1,4)+epsilon/3,F(1,4)-epsilon/6)
        assert pooled==expected and min(pooled)>0 and sum(pooled)==1
        contrast=tuple(p-min(pooled) for p in pooled)
        assert contrast==(F(1,4),epsilon/2,F(0))
    return {'integer_confidence_bounds_checked':trials,'telescoping_union_bounds_checked':100,
            'tree_TV_and_gap_identities_checked':100,'pooled_label_loss_identities_checked':100,'winner_fixtures':fixtures,
            'uniform_tie_abstained':True,'simulated_coverage_trials':0}


def partial_one_program_frontier() -> dict:
    from math import comb
    cases=[]
    for r in range(2,6):
        for b in range(r+1):
            rows=[]
            for chosen in it.combinations(range(r),b):
                for bits in it.product((0,1),repeat=b):
                    row=[None]*r
                    for i,bit in zip(chosen,bits):row[i]=bit
                    rows.append(row)
            assert len(rows)==comb(r,b)*(2**b)
            for g in [F(1,10),F(1,4),F(1,2)]:
                d=F(1,2)-g
                optimum=g*g+2*g*d*F(b,r)+d*d*F(b*(b-1),r*(r-1))
                attained=[]
                for i,j,a,c in pair_cells(r):
                    for qi,qj in it.product((g,1-g),repeat=2):
                        total=F(0)
                        for row in rows:
                            vi=qi if row[i] is None else F(row[i]==a)
                            vj=qj if row[j] is None else F(row[j]==c)
                            total+=vi*vj
                        total/=len(rows)
                        assert total>=optimum
                        if qi==qj==g:assert total==optimum
                        attained.append(total)
                assert min(attained)==optimum
                cases.append({'r':r,'b':b,'g':str(g),'optimum':str(optimum),'rows':len(rows)})
    return {'exact_design_cases':len(cases),'r_values':[2,3,4,5],'g_values':['1/10','1/4','1/2'],'every_b_tested':True,
            'r4_g_one_tenth':{str(c['b']):c['optimum'] for c in cases if c['r']==4 and c['g']=='1/10'},
            'status':'construction and all pair/corner values checked; universal optimality uses manuscript symmetry proof'}


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: the exact checks require assertions.")
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='checks.json');args=parser.parse_args()
    syl=[]
    for r in range(2,33):
        rows=sylvester_design(r);w=[F(1,len(rows))]*len(rows)
        assert set(margins(rows,w))=={F(1,4)}
        assert len(set(rows))==len(rows) and r+1<=len(rows)<2*(r+1)
        syl.append({'r':r,'support':len(rows),'margin':'1/4'})
    # Walsh characters of order <=2 are orthogonal to the degree-3/4 basis.
    X=list(it.product((-1,1),repeat=4));low=[()] + [(i,) for i in range(4)] + list(it.combinations(range(4),2))
    high=list(it.combinations(range(4),3))+[tuple(range(4))]
    def chi(x:tuple[int,...],S:tuple[int,...])->int:
        value=1
        for i in S:value*=x[i]
        return value
    for a in low:
        for b in high:assert sum(chi(x,a)*chi(x,b) for x in X)==0
    out={'packet':'G7-MAXIMAL-20261001','arithmetic':'integer/Fraction only; no floating optimization',
         'five_configuration_exact_certificate':five_row_certificate(),
         'max_margin_designs':{'cases':len(syl),'r_min':2,'r_max':32,'all_pair_margins':'1/4','support':'2^ceil(log2(r+1))'},'four_bit_fourier_orthogonality_checks':len(low)*len(high),
         'collision_and_padding':collision_and_padding(),'statistical_controls':exact_statistical_controls(),
         'one_program_partial_control_frontier':partial_one_program_frontier(),
         'not_executed':['general source census','general quantifier elimination','all finite optimal cost values','independent review','Lean/Isabelle formalization of this packet']}
    text=json.dumps(out,indent=2,sort_keys=True)+'\n';Path(args.output).write_text(text)
    print(json.dumps({'status':'PASS','output':args.output,'sha256':hashlib.sha256(text.encode()).hexdigest(),
                      'five_row_supports':out['five_configuration_exact_certificate']['covering_support_counts'],
                      'padded_graphs':out['collision_and_padding']['padded_graphs_checked'],
                      'switchings':out['collision_and_padding']['switchings_checked']}))

if __name__=='__main__':main()
