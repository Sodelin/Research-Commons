"""Exact executed controls for the G7 continuous-design continuation."""
from __future__ import annotations
import json
from pathlib import Path
from itertools import product
from math import comb
import sympy as s
from law_compiler import (Network, compile_law, unrooted_law, edge_kernel,
                          path_polynomial, forest, evaluate)

TRIANGLE = Network((('R','D'),('R','U'),('U','V'),('U','H'),('V','C'),
                    ('V','H'),('H','W'),('W','A'),('W','B')), 'R', ('A','B','C','D'))
DIAMOND = Network((('R','B'),('R','U'),('U','V'),('U','W'),('V','C'),
                   ('V','H'),('W','D'),('W','H'),('H','A')), 'R', ('A','B','C','D'))
PAIR = Network((('R','D'),('R','v3'),('v3','v2'),('v3','HA'),('v2','v1'),
                ('v2','HC'),('v1','v0'),('v1','HA'),('v0','B'),('v0','HC'),
                ('HA','A'),('HC','C')), 'R', ('A','B','C','D'))
SPLITS = [((('A','B'),('C','D')),), ((('A','C'),('B','D')),), ((('A','D'),('B','C')),)]


def add_bigon(net, leaf, number):
    edges = list(net.edges)
    edge = next(i for i, (_, v) in enumerate(edges) if v == leaf)
    parent, _ = edges.pop(edge)
    u, h = f'padT{number}', f'padH{number}'
    edges.extend(((parent, u), (u, h), (u, h), (h, leaf)))
    return Network(tuple(edges), net.root, net.leaves)


def quartet(net, mode='independent', forced=None, **kwargs):
    return unrooted_law(compile_law(net, mode, forced, **kwargs))


def check():
    report = {'status': 'PASS', 'scope': 'supplied-source compiler and exact finite controls; not a complete source census or independent review'}
    x = s.Symbol('x')
    for k in range(1, 7):
        kernel = edge_kernel(forest(tuple(map(str, range(k)))), x)
        assert s.expand(sum(p for _, p in kernel)) == 1
        for j in range(1, k + 1):
            h = path_polynomial(k, j, x)
            assert s.expand(h.subs(x, 1)) == int(k == j)
            # d/dt h_kj = h_k,j+1 - C(j,2) h_kj, x=exp(-t).
            rhs = -comb(j, 2)*h + (path_polynomial(k, j+1, x) if j < k else 0)
            assert s.expand(-x*s.diff(h, x) - rhs) == 0
    report['edge_kernel_lineage_counts'] = [1, 2, 3, 4, 5, 6]
    report['path_initial_value_and_ODE_cases'] = 21

    tri = quartet(TRIANGLE)
    xx, gg = TRIANGLE.parameters()
    gamma = gg['H']
    a = 1-xx[6]+xx[6]*(gamma**2*(1-2*xx[3]/3)+(1-gamma)**2*(1-2*xx[5]/3)+2*gamma*(1-gamma)*xx[2]/3)
    assert s.expand(tri[SPLITS[0]] - a) == 0
    assert s.expand(tri[SPLITS[1]] - (1-a)/2) == 0
    assert s.expand(tri[SPLITS[2]] - (1-a)/2) == 0
    sub = {v: s.Rational(9,10) for v in xx}; sub[xx[2]]=s.Rational(1,10); sub[gamma]=s.Rational(1,2)
    p = evaluate(tri, sub)
    dia = quartet(DIAMOND)
    dx, dg = DIAMOND.parameters()
    dsub = {v: s.Rational(4,5) for v in dx}; dsub[dx[2]]=dsub[dx[3]]=s.Rational(177,200); dsub[dg['H']]=s.Rational(1,2)
    q = evaluate(dia, dsub)
    assert p == q
    assert [p[t] for t in SPLITS] == [s.Rational(59,200),s.Rational(141,400),s.Rational(141,400)]
    report['independent_triangle_diamond_collision'] = [str(p[t]) for t in SPLITS]
    report['triangle_formula_compared_symbolically'] = True

    full_partial_cases = 0
    for net in (TRIANGLE, DIAMOND, PAIR):
        hybrids = net.structure()[3]
        xvals = {i: s.Rational(i+3, i+5) for i in range(len(net.edges))}
        gvals = {h: s.Rational(2+j,5+j) for j,h in enumerate(hybrids)}
        for row in product((None,0,1), repeat=len(hybrids)):
            forced = {h:b for h,b in zip(hybrids,row) if b is not None}
            indep = quartet(net, 'independent', forced, edge_values=xvals, inheritance_values=gvals)
            common = quartet(net, 'common', forced, edge_values=xvals, inheritance_values=gvals)
            for law in (indep, common):
                assert sum(law.values()) == 1 and all(p>=0 for p in law.values())
            if len(forced) == len(hybrids):
                assert indep == common
            # Explicit shared-bit mixture, retaining source edge parameters.
            mix = {t:s.S.Zero for t in common}
            for bits in product((0,1), repeat=len(hybrids)):
                if any(bits[hybrids.index(h)] != b for h,b in forced.items()):
                    continue
                weight=s.S.One
                for h,b in zip(hybrids,bits):
                    if h not in forced:
                        weight *= gvals[h] if b==0 else 1-gvals[h]
                law = quartet(net, 'independent', dict(zip(hybrids,bits)), edge_values=xvals, inheritance_values=gvals)
                for t in mix: mix[t] += weight*law[t]
            assert mix == common
            full_partial_cases += 1
    report['partial_row_cases_both_mechanisms'] = full_partial_cases
    report['shared_bit_mixture_comparisons'] = full_partial_cases

    # Symbolic neutral bigon, with arbitrary distinct parallel-edge lengths.
    neutral_cases = 0
    for base, leaf in ((TRIANGLE, 'D'), (DIAMOND,'B')):
        padded = add_bigon(base, leaf, 0)
        old_law = quartet(base)
        oldx, oldg = base.parameters(); newx, newg = padded.parameters()
        # Match surviving non-pendant edge identities; removed pendant variable
        # cancels from the quartet law because it carries only one lineage.
        mapping={oldx[i]:newx[padded.edges.index(e)] for i,e in enumerate(base.edges) if e in padded.edges}
        target = {t:s.expand(poly.subs(mapping, simultaneous=True)) for t,poly in old_law.items()}
        for setting in (None,0,1):
            f={} if setting is None else {'padH0':setting}
            law=quartet(padded, forced=f)
            assert all(s.expand(law[t]-target[t])==0 for t in target)
            neutral_cases+=1
    report['symbolic_pendant_bigon_invariance_cases'] = neutral_cases

    # Additional rooted outputs and multiple sampled lineages on one taxon.
    tree = Network((('R','A'),('R','U'),('U','B'),('U','V'),('V','C'),('V','D')), 'R', ('A','B','C','D'))
    rooted = compile_law(tree, edge_values={i:s.Rational(2,3) for i in range(6)}, samples={'A':('A0','A1'),'B':('B',),'C':('C',),'D':('D',)})
    assert sum(rooted.values())==1 and all(p>=0 for p in rooted.values())
    report['five_copy_tree_rooted_outcomes'] = len(rooted)
    report['five_copy_tree_unrooted_outcomes'] = len(unrooted_law(rooted))
    return report

if __name__ == '__main__':
    result = check()
    path=Path(__file__).with_name('compiler-checks.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
