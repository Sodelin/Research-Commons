"""Exact source arithmetic and real pinned-decoder integration.

Analytical count fixtures lie on a proved coverage event. They are NOT random
data, Monte Carlo coverage validation, or physical-control validation.
Dependencies remain in their original peer packets, with immutable Git hashes.
"""
from fractions import Fraction as F
from hashlib import sha1, sha256
from itertools import combinations, product
from math import lcm, comb
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / '2026-09-30-control-menu-continuation'
sys.path.insert(0, str(PREVIOUS))
import integration_checks as bridge
import menu_checks as menu
from robust_support import Contract, GuardedOracle, certify, sufficient_prefix, radius_squared, RecoveryAbstention
from cf_confidence import ideal_cf_boxes,safe_controller_answer

PINS = {
    'adaptive_order.py': '5ac90d944e104d79d893fb266342806e565bfad9',
    'insertion.py': '88c0b7dd1027d48ebcce6f6d9382602377f3d462',
    'core.py': '2d679d1f284889fb754f2475d6d7c0ec7de47421',
    'recover_all.py': '47ce96e814b904400b04f75045f5fd2c8a9c5bc3',
    'vendor/order_recovery.py': 'ec037ceb66d7f68ef0c76842b78b4f751f9f63c6',
    'vendor/sparse_quartet.py': '49933337ce26ce0d5ef58bbfa458bf5706d8e817',
}


def distance_quartet(edges, units):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, []).append((b, units.get((a,b), 1)))
        adj.setdefault(b, []).append((a, units.get((a,b), 1)))
    dists = {}
    for leaf in 'ABCD':
        dist = {leaf: 0}; todo = [leaf]
        while todo:
            v = todo.pop()
            for w, ell in adj[v]:
                if w not in dist:
                    dist[w] = dist[v] + ell; todo.append(w)
        assert len(dist) == len(adj)
        dists[leaf] = dist
    sums = [dists['A']['B']+dists['C']['D'],
            dists['A']['C']+dists['B']['D'],
            dists['A']['D']+dists['B']['C']]
    t = sums.index(min(sums))
    others = [s for i,s in enumerate(sums) if i != t]
    assert others[0] == others[1] and others[0] > sums[t]
    ell = (others[0]-sums[t])//2
    x = F(1, 2)**ell
    return t, ell, tuple(x/3 + (1-x if j == t else 0) for j in range(3))


def source_obstruction():
    tree = [('R','D'),('R','U'),('U','C'),('U','V'),('V','A'),('V','B')]
    fixed = [('R','D'),('R','U'),('U','V'),('V','A'),('V','W'),('W','B'),('H','C')]
    raw = fixed + [('U','H'),('W','H')]
    vertices = {v for e in raw for v in e}
    for v in vertices:
        deg = (sum(b==v for a,b in raw),sum(a==v for a,b in raw))
        assert deg == ((0,2) if v=='R' else (1,0) if v in 'ABCD' else (2,1) if v=='H' else (1,2))
    seen=set()
    while len(seen)<len(vertices):
        ready={v for v in vertices-seen if all(a in seen for a,b in raw if b==v)}
        assert ready;seen|=ready
    tA, ellA, pA = distance_quartet(tree,{})
    switched = [distance_quartet(fixed+[edge],{('U','V'):2}) for edge in [('U','H'),('W','H')]]
    assert (tA,ellA)==(0,1) and [(t,e) for t,e,p in switched]==[(0,2),(2,1)]
    pB = tuple(F(3,4)*switched[0][2][i]+F(1,4)*switched[1][2][i] for i in range(3))
    assert pA==(F(2,3),F(1,6),F(1,6))
    assert pB==(F(2,3),F(5,48),F(11,48))
    tv = sum(abs(a-b) for a,b in zip(pA,pB))/2
    midpoint=tuple((a+b)/2 for a,b in zip(pA,pB))
    assert tv==F(1,16) and all(sum(abs(a-b) for a,b in zip(p,midpoint))/2==F(1,32) for p in (pA,pB))
    eta=F(1,17); common=(F(32,51),F(8,51),F(11,51))
    contaminants=[tuple((common[i]-(1-eta)*p[i])/eta for i in range(3)) for p in (pA,pB)]
    assert contaminants==[(F(0),F(0),F(1)),(F(0),F(1),F(0))]
    return {'scope':'actual passive four-taxon tree vs one-gall network; source admission manual plus degree/DAG checks',
            'pA':[str(x) for x in pA],'pB':[str(x) for x in pB],
            'gap':'1/8','clean_tv':str(tv),'tv_overlap':'1/32','huber_overlap':'1/17',
            'common_huber_law':[str(x) for x in common]}


def decoder_integration(directory,provider=certify,grid=None):
    for name,pin in PINS.items():
        raw=(directory/name).read_bytes()
        assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==pin,name
    sys.path.insert(0,str(directory))
    from recover_all import recover_all
    cases=[]
    if grid is None:grid=product((2,3,4),(4,5,6),('tv','huber'))
    for r,n,noise in grid:
        edges,hybrids,labels=bridge.fixture(r,(0,1),(1,1),n)
        records=[]
        for bits in product((0,1),repeat=r):
            switched=edges+[(h[1][bits[i]],h[0]) for i,h in hybrids.items()]
            qs,splits=bridge.tree_observations(switched,labels)
            records.append((bits,qs,splits))
        rows=menu.partial_array(r); ps=tuple(F(1,4) for i in range(r))
        support,splits,gap,receipt,_=bridge.analytic_provider(records,rows,ps,labels)
        assert F(gap)>=F(1,8)
        contract=Contract(F(1,8),tuple(F(1,128) for row in rows),noise)
        B=comb(n,4); delta=F(1,20)
        probs={q:[] for q in support}
        for row in receipt:
            for key,p in row['cf'].items():
                q=tuple(key.split()); clean=tuple(F(x) for x in p)
                e=contract.error[0]
                if noise=='tv':
                    observed=(clean[0]-e,clean[1]+e,clean[2])
                    assert min(observed)>=0
                    assert sum(abs(a-b) for a,b in zip(clean,observed))/2==e
                else:
                    observed=tuple((1-e)*clean[i]+(e if i==1 else 0) for i in range(3))
                probs[q].append(observed)
        denom=lcm(*(v.denominator for blocks in probs.values() for row in blocks for v in row))
        prefix=sufficient_prefix(contract,B,delta)
        N=((prefix+denom-1)//denom)*denom
        while 16*radius_squared(N,len(rows),B,delta)>=contract.margin**2:
            N*=2
        counts={q:tuple(tuple(int(N*v) for v in row) for row in blocks) for q,blocks in probs.items()}
        oracle=GuardedOracle(lambda iq:counts[tuple(labels[i] for i in iq)],contract,B,delta,provider=provider)
        answer=recover_all(range(n),oracle)
        truth=frozenset(frozenset(labels.index(x) for x in side) for side in splits)
        expected=frozenset(min(side,frozenset(range(n))-side,key=lambda x:(len(x),tuple(sorted(x)))) for side in truth)
        assert answer.expanded_splits()==expected
        for side in expected:
            memberships=[x in side for x in answer.order]
            assert sum(memberships[i]!=memberships[(i+1)%n] for i in range(n))==2
        for q,mask in oracle.cache.items():
            assert mask==sum(1<<t for t in support[tuple(labels[i] for i in q)])
        # Insufficient data aborts the actual decoder, never returns a tree.
        uncertain=GuardedOracle(lambda q:[(1,1,1)]*len(rows),contract,B,delta,provider=provider)
        try: recover_all(range(n),uncertain)
        except RecoveryAbstention as exc: assert str(exc)=='INCONCLUSIVE'
        else: raise AssertionError('decoder did not abstain')
        cases.append({'r':r,'n':n,'noise':noise,'environments':len(rows),
                      'analytical_prefix':N,'decoder_queries':len(oracle.cache),
                      'split_count':len(expected),'split_and_mask_replay':'passed','low_data_abort':'passed'})
    return cases


def main():
    from law_feasibility import certify as feasible_certify
    directory=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/tmp/astra-query-pinned')
    obstruction=source_obstruction()
    q=tuple('ABCD'); truth=tuple(F(x) for x in obstruction['pB'])
    eps=F(1,128); observed=(truth[0]-eps,truth[1]+eps,truth[2])
    n=1536000;counts={q:tuple(int(n*x) for x in observed)}
    box=ideal_cf_boxes('ABCD',counts,F(1,20),tv_error=eps)
    assert all(box[q][i][0]<=truth[i]<=box[q][i][1] for i in range(3))
    assert ideal_cf_boxes('ABCD',{q:(0,0,0)},F(1,20))[q]==((F(0),F(1)),)*3
    assert safe_controller_answer({'full_class_status':'INCONCLUSIVE','all_class_outer_candidates':'ALL_ADMITTED_TARGETS','solver_feasible_targets':{1}})['status']=='INCONCLUSIVE'
    assert safe_controller_answer({'full_class_status':'unique','all_class_outer_candidates':{1}})=={'status':'CERTIFIED','target':1}
    assert safe_controller_answer({'full_class_status':'unique','all_class_outer_candidates':{1,2}})['status']=='INCONCLUSIVE'
    assert safe_controller_answer({'full_class_status':'infeasible','all_class_outer_candidates':set()})['status']=='MODEL_INCOMPATIBLE'
    report={'session':'ROBUST-STAT-20260930-1620Z','source_obstruction':obstruction,
            'decoder_dependency_blobs':PINS,'decoder_integration':decoder_integration(directory),
            'feasible_provider_decoder_integration':decoder_integration(directory,feasible_certify,product((4,),(4,5,6),('tv','huber'))),
            'scope':'exact analytical coverage-event counts, source arithmetic, pinned real joint decoder; no Monte Carlo/physical verification',
            'passive_cf_bridge':'outward box contains true source CF under certified bias; zero-data and incomplete/unknown/contradictory-controller guards passed; API matched by source inspection, peer solver not executed',
            'code_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE/'checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'source_obstruction':report['source_obstruction'],
                      'decoder_runs':len(report['decoder_integration']),
                      'feasible_provider_decoder_runs':len(report['feasible_provider_decoder_integration']),'all':'passed'},indent=2))

if __name__=='__main__':
    if not __debug__:raise RuntimeError('run without -O')
    main()
