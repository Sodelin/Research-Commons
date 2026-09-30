"""Finite exact tests against formulas, tree edge mixtures, and published provider.

This is not full enumeration of source networks and is not a proof by testing.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import json
import random
import sys
from control_protocol import Network, Edge, cf, compile_row, contrast, triangle, triangle_formula, topology, indistinguishable_diamond, sample_identifier_environment


def tree_mixture(net, taxa, fixed):
    """Independent tree-edge split formula, rather than the first-merger recursion."""
    answer, supports = [F(0)] * 3, set()
    hs = sorted(net.inheritance)
    for bits in product((0,1), repeat=len(hs)):
        assignment = dict(zip(hs,bits))
        if any(assignment[h] != b for h,b in fixed.items()):
            continue
        chance = F(1)
        for h,b in assignment.items():
            if h not in fixed:
                p = net.inheritance[h]
                chance *= p if b == 0 else 1-p
        selected = {h: net.incoming(h)[b].name for h,b in assignment.items()}
        edges = [e for e in net.edges if e.child not in selected or selected[e.child] == e.name]
        adj = {}
        for e in edges:
            adj.setdefault(e.parent,set()).add(e.child)
            adj.setdefault(e.child,set()).add(e.parent)
        assert len(edges) == len(adj)-1
        resolve, survival = None, F(1)
        for e in edges:
            seen, todo = {e.parent}, [e.parent]
            while todo:
                v = todo.pop()
                for w in adj[v]:
                    if {v,w} == {e.parent,e.child}:
                        continue
                    if w not in seen:
                        seen.add(w); todo.append(w)
            side = {label for v,label in net.leaves.items() if v in seen and label in taxa}
            if len(side) == 2:
                here = topology(sum(1 << taxa.index(t) for t in side))
                if resolve is not None:
                    assert resolve == here
                resolve = here; survival *= e.survival
        assert resolve is not None
        supports.add(resolve)
        for j in range(3):
            answer[j] += chance * (1-F(2,3)*survival if j == resolve else survival/3)
    assert sum(answer) == 1
    return tuple(answer), supports


def counts(law, n):
    result = [p*n for p in law]
    assert all(p.denominator == 1 for p in result)
    return tuple(int(p) for p in result)


def main():
    net = triangle(bigons=1)
    source = net.structural_checks()
    assert net.descendant_counts() == {'H':2,'J0':1}
    expected = (F(59,200),F(141,400),F(141,400))
    repaired = (F(23,50),F(27,100),F(27,100))
    for bit in (0,1):
        row = {'H':None,'J0':bit}
        assert cf(net,'ABCD',fixed={'J0':bit}) == expected
        assert compile_row(net,row).synchronize == ('H',)
        assert compile_row(net,row).expanded_quartet_law('ABCD') == repaired
        assert cf(net,'ABCD',fixed={'H':bit}) == repaired
        assert tree_mixture(net,tuple('ABCD'),{'J0':bit})[1] == {0}
    assert contrast(expected) == (F(0),F(23,400),F(23,400))
    assert triangle_formula(F(9,10),F(9,10),F(9,10),F(1,10),F(1,2)) == expected
    competitor = indistinguishable_diamond()
    competitor.structural_checks()
    for bit in (0,1):
        assert cf(competitor,'ABCD',fixed={'J0':bit}) == expected
        assert tree_mixture(competitor,tuple('ABCD'),{'J0':bit})[1] == {1,2}
    assert competitor.descendant_counts() == {'H':1,'J0':1}

    formula_checks = 0
    for x0,u,v,w in product((F(1,4),F(9,10)), repeat=4):
        for gamma in (F(1,5),F(1,2),F(4,5)):
            base = triangle()
            substitutions = {('H','W'):x0,('U','H'):u,('V','H'):v,('U','V'):w}
            new = Network(tuple(Edge(e.parent,e.child,substitutions.get((e.parent,e.child),e.survival),e.name)
                                for e in base.edges),dict(base.leaves),{'H':gamma})
            assert cf(new,'ABCD') == triangle_formula(x0,u,v,w,gamma)
            formula_checks += 1

    fixture_checks, row_quartets, marginal_checks = [], 0, 0
    for bigons in (0,1,2):
        for extra in range(4):
            model = triangle(bigons=bigons,extra_outgroup_taxa=extra)
            record = model.structural_checks()
            hs = sorted(model.inheritance)
            # Every partial row on this small fixture: direct interventions and
            # an independent tree-mixture calculation jointly test compilation.
            for values in product((None,0,1), repeat=len(hs)):
                row = dict(zip(hs,values))
                fixed = {h:b for h,b in row.items() if b is not None}
                known = compile_row(model,row)
                fallback = compile_row(model,row,graph_known=False)
                for q in combinations(sorted(model.leaves.values()),4):
                    desired = cf(model,q,fixed=fixed,shared=hs)
                    assert known.expanded_quartet_law(q) == desired
                    assert fallback.expanded_quartet_law(q) == desired
                    independent_tree_law, support = tree_mixture(model,q,fixed)
                    assert desired == independent_tree_law
                    assert all((desired[j]-min(desired) > 0) == (j in support) for j in range(3))
                    row_quartets += 1
                    marginal_checks += 3
            record['sample_descendants'] = model.descendant_counts()
            fixture_checks.append(record)

    # Actual robust provider integration. These are rational law/count fixtures,
    # not simulated or observed experimental genes. The pre-repair call violates
    # its scientific premises; it demonstrates the consequence of that misuse.
    old = Path(__file__).resolve().parents[1]/'2026-09-30-robust-statistical-recovery'
    sys.path.insert(0,str(old))
    from robust_support import Contract, certify
    contract = Contract(F(1,20),(F(0),F(0)))  # g=.5 and original x<=.9 give tau=-ln(.9)
    n = 40_000_000
    wrong = certify([counts(expected,n)]*2,contract,1,F(1,100),anytime=False)
    correct = certify([counts(repaired,n)]*2,contract,1,F(1,100),anytime=False)
    assert wrong.mask == 6 and correct.mask == 1
    noisy_provider = []
    for noise in ('tv','huber'):
        c = Contract(F(1,20),(F(1,1000),F(1,1000)),noise=noise)
        good = certify([counts(repaired,n)]*2,c,1,F(1,100),anytime=False)
        assert good.mask == 1
        noisy_provider.append({'noise':noise,'certified_mask':good.mask,'margin':str(c.margin)})
    small = certify([counts(repaired,100)]*2,contract,1,F(1,100),anytime=False)
    assert small.status == 'INCONCLUSIVE'

    # Taxon count must be replaced by copy count if sampling changes.
    doubled = {t:1 for t in net.leaves.values()}; doubled['D'] = 2
    assert compile_row(net,{'H':None,'J0':None},sample_copies=doubled).synchronize == ('H','J0')
    assert compile_row(net,{'H':None,'J0':None}).synchronize == ('H',)
    zero = {t:0 for t in net.leaves.values()}
    assert compile_row(net,{'H':None,'J0':None},sample_copies=zero).synchronize == ()
    for method in ('expanded_quartet_law','two_configuration_quartet_law'):
        try:
            getattr(compile_row(net,{'H':None,'J0':None},sample_copies=zero),method)('ABCD')
        except ValueError:
            pass
        else:
            raise AssertionError('verifier accepts undeclared sampled taxa')
    rng = random.Random(1810)
    compiled = compile_row(net,{'H':None,'J0':1})
    emitted = [compiled.sample_environment(rng) for _ in range(100)]
    assert {x['H'] for x in emitted} == {0,1} and all(x['J0'] == 1 for x in emitted)
    two_vectors = [compiled.sample_two_configuration_environment(rng) for _ in range(100)]
    assert {tuple(sorted(x.items())) for x in two_vectors} == {
        (('H',0),('J0',1)),(('H',1),('J0',1))}
    assert compiled.two_configuration_quartet_law('ABCD') == repaired
    graph_free = [sample_identifier_environment({'H':None,'J0':1},net.inheritance,rng,
                                               two_configurations=True) for _ in range(100)]
    assert {tuple(sorted(x.items())) for x in graph_free} == {
        (('H',0),('J0',1)),(('H',1),('J0',1))}
    bad_rows = ({'H':None},{'H':True,'J0':None},{'H':2,'J0':None},{'H':.5,'J0':None})
    for row in bad_rows:
        try:
            compile_row(net,row)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid row accepted')
    try:
        compiled.expanded_quartet_law('ABCD',verification_site_cap=0)
    except ValueError:
        pass
    else:
        raise AssertionError('uncapped expansion')
    result = {'status':'PASS','formula_checks':formula_checks,'source_fixtures':fixture_checks,
              'partial_row_quartet_comparisons':row_quartets,'law_comparisons':marginal_checks,
              'natural_cf':list(map(str,expected)),'compiled_cf':list(map(str,repaired)),
              'controlled_profile_competitor_support':[1,2],
              'original_controlled_profile_support':[0],
              'equal_controlled_unrooted_gene_topology_laws':True,
              'naive_provider_wrong_mask':wrong.mask,'compiled_provider_correct_mask':correct.mask,
              'provider_noise_checks':noisy_provider,'low_data':small.status,
              'invalid_row_cases':len(bad_rows),'random_schedule_draws':len(emitted),
              'not_executed':['full source-network enumeration','full joint gene-law enumeration',
                              'formal proof','physical intervention'],
              'source_admission':'degree/LSA/cut checks + written outer-face fixture proof'}
    Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='source_fixtures'},indent=2))


if __name__ == '__main__':
    main()
