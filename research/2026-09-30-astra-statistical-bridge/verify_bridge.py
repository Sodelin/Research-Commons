"""Exact finite regression checks, not Lean verification or a proof by sampling."""
from __future__ import annotations
import hashlib
import itertools
import json
from fractions import Fraction as F
from math import exp, log
from pathlib import Path
from statistical_bridge import (
    cf_support, no_ils_support, fixed_cf_loci, fixed_no_ils_loci,
    streaming_cf_loci, streaming_no_ils_loci, cf32,
)


def transcript(truth, estimates=None, variant=0):
    """Depth-three adaptive discrete decision tree; estimates indexed (step,q)."""
    node, out = 0, []
    for j in range(3):
        q = (node + variant*j) % 3
        bit = truth[q] if estimates is None else estimates[3*j + q]
        out.append((q, bit))
        node = 2*node + 1 + bit
    return out


def first_divergence_checks():
    checked = 0
    for variant in range(3):
        for truth in itertools.product((0, 1), repeat=3):
            ideal = transcript(truth, variant=variant)
            for estimates in itertools.product((0, 1), repeat=9):
                actual = transcript(truth, estimates, variant)
                errors_on_fixed_path = [estimates[3*j+q] != truth[q] for j,(q,_) in enumerate(ideal)]
                errors_on_actual_path = [answer != truth[q] for q,answer in actual]
                assert any(errors_on_actual_path) == any(errors_on_fixed_path)
                if any(errors_on_actual_path):
                    j = errors_on_actual_path.index(True)
                    assert actual[:j] == ideal[:j] and actual[j][0] == ideal[j][0]
                checked += 1
    return checked


def graph_data():
    edges = [('R','P'),('R','D'),('P','Q'),('P','H'),('Q','C'),('Q','H'),('H','S'),('S','A'),('S','B')]
    # Rotation system after suppressing degree-two root R.
    rotation = {'P':['Q','H','D'], 'Q':['H','P','C'], 'H':['S','P','Q'],
                'S':['B','A','H'], 'A':['S'], 'B':['S'], 'C':['Q'], 'D':['P']}
    return edges, rotation


def cyclic_canonical(xs):
    xs = tuple(xs)
    rots = [xs[i:]+xs[:i] for i in range(len(xs))]
    rev = xs[::-1]
    rots += [rev[i:]+rev[:i] for i in range(len(rev))]
    return min(rots)


def faces(rotation):
    seen, result = set(), []
    for u in rotation:
        for v in rotation[u]:
            if (u,v) in seen:
                continue
            start, dart, cycle = (u,v), (u,v), []
            while dart not in seen:
                seen.add(dart)
                a,b = dart
                cycle.append(b)
                neigh = rotation[b]
                dart = (b, neigh[(neigh.index(a)-1) % len(neigh)])
            assert dart == start
            result.append(cycle)
    return result


def splits_of_tree(edges, taxa):
    adj = {}
    for a,b in edges:
        adj.setdefault(a,set()).add(b)
        adj.setdefault(b,set()).add(a)
    assert len(edges) == len(adj)-1
    splits = set()
    for a,b in edges:
        todo, seen = [a], {a}
        while todo:
            u = todo.pop()
            for v in adj[u]:
                if {u,v} == {a,b} or v in seen:
                    continue
                seen.add(v); todo.append(v)
        part = set(taxa) & seen
        other = set(taxa)-part
        if len(part) == len(other) == 2:
            splits.add(tuple(sorted((''.join(sorted(part)), ''.join(sorted(other))))))
    return splits


def graph_checks():
    edges, rotation = graph_data()
    vertices = set(itertools.chain.from_iterable(edges))
    indeg = {v:sum(b==v for a,b in edges) for v in vertices}
    outdeg = {v:sum(a==v for a,b in edges) for v in vertices}
    assert (indeg['R'],outdeg['R']) == (0,2)
    assert (indeg['H'],outdeg['H']) == (2,1)
    for t in 'ABCD': assert (indeg[t],outdeg[t]) == (1,0)
    for v in ('P','Q','S'): assert (indeg[v],outdeg[v]) == (1,2)
    todo, count, degree = ['R'], 0, indeg.copy()
    while todo:
        v = todo.pop(); count += 1
        for a,b in edges:
            if a == v:
                degree[b] -= 1
                if degree[b] == 0: todo.append(b)
    assert count == len(vertices)
    # The connected underlying graph has cycle rank one, with cycle P-Q-H-P.
    assert len(edges)-len(vertices)+1 == 1
    supports=[]; orders=[]
    for relabel in ({x:x for x in 'ABCD'}, {'A':'A','B':'D','C':'C','D':'B'}):
        rename=lambda x:relabel.get(x,x)
        support=set()
        for dropped in [('P','H'),('Q','H')]:
            selected=[(rename(a),rename(b)) for a,b in edges if (a,b)!=dropped]
            support |= splits_of_tree(selected, set('ABCD'))
        rr={rename(a):[rename(b) for b in ns] for a,ns in rotation.items()}
        ff=faces(rr)
        assert len(ff)==2
        outer=[f for f in ff if any(v in 'ABCD' for v in f)]
        assert len(outer)==1
        leaves=[v for v in outer[0] if v in 'ABCD']
        assert sorted(leaves)==list('ABCD')
        order=cyclic_canonical(leaves)
        assert order==tuple('ABCD')
        supports.append(sorted(support)); orders.append(''.join(order))
    assert supports == [[('AB','CD')], [('AD','BC')]]
    return {'source_class_checks':'binary DAG; root LSA via pendant root child; one gall; explicit outer-face order; both switchings',
            'displayed_supports':supports, 'common_order':orders,
            'graph_edges':edges, 'rotations_after_root_suppression':rotation}


def classifier_checks():
    cases=[((F(1,2),F(1,4),F(1,4)),F(1,4),{0}),
           ((F(1,4),F(1,4),F(1,2)),F(1,4),{2}),
           ((F(2,5),F(1,5),F(2,5)),F(1,5),{0,2}),
           ((F(1,4),F(3,8),F(3,8)),F(1,8),{0}),
           ((F(3,8),F(3,8),F(1,4)),F(1,8),{2})]
    total=inside=0
    for p,g,expected in cases:
        for m in range(1,41):
            for a in range(m+1):
                for b in range(m-a+1):
                    counts=(a,b,m-a-b)
                    errors=[abs(F(counts[t]-counts[1],m)-(p[t]-p[1])) for t in (0,2)]
                    answer=cf_support(counts,g)
                    if max(errors)<g/2:
                        assert answer==expected
                        inside+=1
                    total+=1
    # Negative contrast must not be discarded.
    assert cf_support((2,3,3),F(1,8))=={0}
    assert no_ils_support((1,0,1))=={0,2}
    try: no_ils_support((1,1,1))
    except ValueError: pass
    else: raise AssertionError('NMSC support must not pass the no-ILS guard')
    return {'rational_count_states':total,'states_inside_proved_contrast_event':inside,'source_case_count':len(cases)}


def calibration_checks():
    checked=0
    for d in (.1,.05,.01):
        for g in (.1,.25,.5,1.):
            for b in (1,2,10,100):
                m=fixed_cf_loci(g,b,d)
                assert 4*b*exp(-m*g*g/8) <= d*(1+1e-12)
                checked+=1
        for rho in (.01,.1,.5,.99,1.):
            for b in (1,2,10,100):
                m=fixed_no_ils_loci(rho,b,d)
                assert 2*b*(1-rho)**m <= d*(1+1e-12)
                checked+=1
        for j in range(1,31):
            budget=d/(j*(j+1))
            assert 4*exp(-streaming_cf_loci(.2,j,d)*.2**2/8) <= budget*(1+1e-12)
            assert 2*.9**streaming_no_ils_loci(.1,j,d) <= budget*(1+1e-12)
            checked+=2
    # Known law of missing one of two displayed alternatives.
    for rho in (F(1,2),F(1,4),F(1,10)):
        for m in range(1,31):
            assert rho**m+(1-rho)**m <= 2*(1-rho)**m
            checked+=1
    return checked


def run():
    uniform=cf32(F(40,47),F(9,10),F(1,10),F(9,10))
    negative=cf32(F(45,47),F(9,10),F(1,10),F(9,10))
    assert uniform==(F(1,3),)*3 and negative==(F(1,4),F(3,8),F(3,8))
    j=16
    # Negative control: raw-data-dependent query selection destroys fixed-path bound.
    fixed_query_errors=[sum(z==q for z in range(j))/j for q in range(j)]
    selected_error=sum(z==z for z in range(j))/j
    assert max(fixed_query_errors)==1/j and selected_error==1
    report={
        'session':'ASTRA-STAT-20260930-0942Z',
        'verification':'finite exact regression checks; NOT Lean; no empirical biological validation',
        'first_divergence_arbitrary_error_tables':first_divergence_checks(),
        'classifier':classifier_checks(),
        'calibration_assertions':calibration_checks(),
        'uniform_source_cf':[str(x) for x in uniform],
        'negative_contrast_source_cf':[str(x) for x in negative],
        'source_x':[str(x) for x in (F(40,47),F(9,10),F(1,10),F(9,10))],
        'positive_source_lengths':[-log(float(x)) for x in (F(40,47),F(9,10),F(1,10),F(9,10))],
        'graph':graph_checks(),
        'data_snooping_negative_control':{'queries':j,'each_fixed_query_error':1/j,'data_selected_query_error':selected_error},
        'streaming_example':{'delta':.05,'last_query':100,'no_ils_min_mass':.1,
                             'no_ils_loci':streaming_no_ils_loci(.1,100,.05),
                             'cf_min_gap':.1,'cf_loci':streaming_cf_loci(.1,100,.05)},
        'source_formula_provenance':'Allman, Banos, Rhodes 2019, equation before Proposition 10; xi labels follow source Figure 5',
        'file_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(__file__).with_name('statistical_bridge.py')]},
    }
    out=Path(__file__).with_name('verification.json')
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    if not __debug__: raise RuntimeError('Run without -O: assertions are checks')
    run()
