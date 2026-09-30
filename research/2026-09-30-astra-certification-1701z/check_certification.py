"""Reproducible exact controls, not an unbounded source-class census or peer review."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import hashlib
import json
import platform
import sys
import time
import networkx as nx
import sympy as sp
from certification import *
from cf_normal_form import common_cf_by_tree_mixture, switched_trees

HERE = Path(__file__).resolve().parent


def unrooted_trees(n):
    """Every labeled unrooted binary topology, by unique last-leaf deletion."""
    g = nx.Graph(); g.add_edges_from(('u0', f't{i}') for i in range(3))
    trees = [g]
    for size in range(4, n+1):
        new = []
        for tree in trees:
            for a, b in sorted(tree.edges()):
                out = tree.copy(); out.remove_edge(a, b)
                out.add_edges_from([(a, f'u{size-3}'), (b, f'u{size-3}'),
                                    (f'u{size-3}', f't{size-1}')])
                new.append(out)
        trees = new
    return trees


def root_tree(tree, root_edge_index=0):
    g = tree.copy()
    a, b = sorted(g.edges())[root_edge_index % len(g.edges())]
    g.remove_edge(a, b); g.add_edges_from([('ROOT', a), ('ROOT', b)])
    arcs = list(nx.bfs_edges(g, 'ROOT'))
    net = Network([Edge(a, b, F(1, 4), f'e{i}') for i, (a, b) in enumerate(arcs)],
                  {x: x for x in g if x.startswith('t')}, {})
    net.source_check(); return net


def transfer(tree: Network, leaf: str, donor: str, epsilon=F(1, 7)):
    if not 0 < epsilon < 1 or leaf == donor or tree.inheritance:
        raise ValueError('this fixture requires a tree and interior terminal transfer')
    ea, ec = tree.incoming(leaf)[0], tree.incoming(donor)[0]
    # Fixture edges have survival 1/4, split into two positive 1/2 edges.
    if ea.survival != F(1, 4) or ec.survival != F(1, 4):
        raise ValueError('fixture subdivision assumption')
    es = [e for e in tree.edges if e not in (ea, ec)]
    es += [Edge(ea.parent, 'NEW_H', F(1, 2), 'new_a_in'),
           Edge('NEW_H', leaf, F(1, 2), 'new_a_out'),
           Edge(ec.parent, 'NEW_Q', F(1, 2), 'new_c_in'),
           Edge('NEW_Q', donor, F(1, 2), 'new_c_out'),
           Edge('NEW_Q', 'NEW_H', F(1, 3), 'new_minor')]
    net = Network(es, tree.leaves.copy(), {'NEW_H': 1-epsilon})
    net.source_check(); return net


def main(part='all'):
    receipt = {'session': 'ASTRA-CERTIFICATION-20260930-1701Z',
               'kind': 'exact algebraic and source controls; conditional mathematics, not independent review'}
    fixtures = {}
    if part in ('all', 'solver'):
        start = time.monotonic()
        points = {(F(i, 12), F(j, 12), F(12-i-j, 12))
                  for i in range(1, 12) for j in range(1, 12-i)}
        points |= {(F(1), F(0), F(0)), (F(0), F(1, 2), F(1, 2)),
                   (F(1, 6), F(5, 12), F(5, 12)), (F(1, 3),)*3}
        count = 0
        for mechanism in ('ind', 'com'):
            for closure in (False, True):
                for point in sorted(points):
                    observed = set()
                    for label, variables, probs in four_taxon_images(mechanism):
                        script = polynomial_image_smt(variables, probs, point, closure=closure)
                        answer = solve_in_process(script)
                        if answer not in ('sat', 'unsat'): raise AssertionError(answer)
                        if answer == 'sat': observed.add(label)
                        count += 1
                    assert observed == local_fiber_formula(point, mechanism, closure), (point, observed)
        receipt['six_image_solver_grid'] = {'points': len(points), 'mechanisms': 2, 'domains': 2,
                                             'individual_solver_verdicts': count}
        cases = {}
        for name, p in [('tree', (F(2, 3), F(1, 6), F(1, 6))),
                        ('threshold', (F(1, 6), F(5, 12), F(5, 12))),
                        ('below_threshold', (F(1, 8), F(7, 16), F(7, 16))),
                        ('distinct', (F(1, 2), F(1, 3), F(1, 6))),
                        ('uniform', (F(1, 3),)*3)]:
            cases[name] = {m: {'exact': sorted(local_fiber_formula(p, m)),
                               'robust': sorted(local_fiber_formula(p, m, True))} for m in ('ind', 'com')}
        assert cases['threshold']['ind'] == {'exact': ['D12'], 'robust': ['D12', 'T0']}
        assert cases['tree']['com'] == {'exact': ['T0'], 'robust': ['D01', 'D02', 'T0']}
        receipt['boundary_classification'] = cases

        # Algebraic input: a=sqrt(1/2), b=(1-a)/2 are encoded independently by
        # unique roots, so there is no floating point equality substitution.
        a = Algebraic((2, 0, -1), '7/10', '4/5')
        b = Algebraic((8, -8, 1), '1/8', '1/6')
        expected = {'T0': 'sat', 'T1': 'unsat', 'T2': 'unsat',
                    'D01': 'unsat', 'D02': 'unsat', 'D12': 'unsat'}
        algebraic = {}
        for label, variables, probs in four_taxon_images('com'):
            script = polynomial_image_smt(variables, probs, [a, b, b])
            answer = solve_in_process(script); assert answer == expected[label]
            algebraic[label] = answer
            fixtures['algebraic_'+label] = script
        receipt['algebraic_input'] = algebraic
        invalid = 0
        for bad in [Algebraic((1, 0, -2), '-2', '2'), Algebraic((1, 0, -2), '0', '1'),
                    Algebraic((1, 0, -1), '1', '2'), Algebraic((0, 1), '0', '1')]:
            try: bad.validated()
            except ValueError: invalid += 1
            else: raise AssertionError('invalid algebraic input accepted')
        try: rational(.1)
        except ValueError: invalid += 1
        else: raise AssertionError('binary float accepted')
        receipt['invalid_exact_encodings_rejected'] = invalid

        # At p=(1/2,1/3,1/6), exact distance to every different support image is >=1/12,
        # and a rival touches the closed box at 1/12. All six image sets are checked.
        p = (F(1, 2), F(1, 3), F(1, 6)); delta = F(1, 12)
        distance_results = {}
        for mech in ('ind', 'com'):
            records = []
            for radius in (delta-F(1, 1000), delta):
                box = [(x-radius, x+radius) for x in p]
                result = local_box_candidates(box, mech)
                records.append({'radius': str(radius), 'candidates': result['outer_candidates']})
                if radius < delta: assert result['outer_candidates'] == ['D01']
                else: assert len(result['outer_candidates']) > 1
            distance_results[mech] = records
        receipt['exact_separation_radius'] = {'point': list(map(str, p)), 'delta': '1/12', 'checks': distance_results}

        tree = root_tree(unrooted_trees(4)[0])
        # For this tree choose an unrooted cherry, then transfer one member to another leaf.
        ug = unrooted_trees(4)[0]
        cherry = next(sorted(v for v in ug.neighbors(u) if v.startswith('t'))
                      for u in ug if len([v for v in ug.neighbors(u) if v.startswith('t')]) >= 2)
        leaf = cherry[0]; donor = min(set(tree.leaves)-set(cherry))
        net = transfer(tree, leaf, donor)
        quartet = tuple(sorted(tree.leaves)); point = cf(tree, quartet)
        actual_graph = {}
        for mechanism in ('ind', 'com'):
            for closure in (False, True):
                script = graph_image_smt(net, {quartet: point}, mechanism=mechanism, closure=closure)
                answer = solve_in_process(script)
                assert answer == ('sat' if closure else 'unsat')
                key = f'actual_diamond_{mechanism}_'+('closure' if closure else 'interior')
                actual_graph[key] = answer; fixtures[key] = script
        receipt['actual_source_graph_boundary'] = actual_graph
        # Shared parameter negative control: separately satisfiable coordinates
        # F(u)=(u,u) cannot fit (1/4,3/4) simultaneously.
        u = sp.Symbol('u')
        shared = polynomial_image_smt([u], [u, u], ['1/4', '3/4'], closure=True)
        assert solve_in_process(shared) == 'unsat'
        fixtures['shared_parameter_contradiction'] = shared
        receipt['shared_parameter_negative_control'] = 'unsat'
        receipt['solver_elapsed_seconds'] = round(time.monotonic()-start, 3)

    if part in ('all', 'trees'):
        count, vector_checks, independent_mixture_checks = 0, 0, 0
        per_size = {}
        for n, expected_count in ((4, 3), (5, 15), (6, 105)):
            trees = unrooted_trees(n); assert len(trees) == expected_count
            seen = set()
            for index, ug in enumerate(trees):
                tree = root_tree(ug, index)
                base = support(tree); assert base not in seen; seen.add(base)
                cherry = next(sorted(v for v in ug.neighbors(u) if v.startswith('t'))
                         for u in ug if len([v for v in ug.neighbors(u) if v.startswith('t')]) >= 2)
                leaf = cherry[0]; donor = min(set(tree.leaves)-set(cherry))
                epsilon = F(1, 7)
                net = transfer(tree, leaf, donor, epsilon)
                target = support(net); assert base < target
                # Minor switching population graph retains unary vertices/root
                # where present. Its conditional law need not be retargeted.
                minor_edges = [e for e in net.edges if e.name != 'new_a_in']
                minor = Network(minor_edges, net.leaves.copy(), {})
                for q in tree.quartets():
                    original = cf(tree, q)
                    secondary = cf(minor, q)
                    expected = tuple((1-epsilon)*x+epsilon*y for x, y in zip(original, secondary))
                    for mech in ('ind', 'com'):
                        actual = cf(net, q, mech); assert actual == expected
                        vector_checks += 1
                    assert common_cf_by_tree_mixture(net, q) == expected
                    independent_mixture_checks += 1
                count += 1
            per_size[str(n)] = len(seen)
        receipt['source_leaf_transfer'] = {'all_unrooted_binary_tree_topologies_in_tested_sizes': per_size,
                      'admitted_tree_plus_reticulation_pairs': count,
                      'exact_mechanism_specific_quartet_vector_equalities': vector_checks,
                      'separate_switched_tree_formula_equalities': independent_mixture_checks,
                      'not_claimed': 'full joint n-gene law was proved by conditioning, not enumerated in these tests'}

    if part in ('all', 'guards'):
        radius_checks = 0
        for dim in (3, 15, 210):
            for m in (1, 2, 10, 100, 1000, 10000, 100000, 10**8):
                radius = radius_bound(dim, m)
                # Check the stronger integer-log bound directly, with no floating point.
                A = F(2*dim*m*(m+1), 1)/F(1, 20)
                L = max(0, A.numerator.bit_length()-A.denominator.bit_length())
                if (1<<L)*A.denominator < A.numerator: L += 1
                assert radius == 1 or 2*m*radius*radius >= L
                assert (1<<L)*A.denominator >= A.numerator
                radius_checks += 1
        box_state = PrefixBoxes(1)
        trajectory = []
        p = (F(1, 2), F(1, 3), F(1, 6))
        old = set(label for label, *_ in four_taxon_images('ind'))
        for m in (60, 600, 6000, 12000):
            result = box_state.update(m, [[m//2, m//3, m//6]])
            assert not result['empty'] and all(lo <= x <= hi for x, (lo, hi) in zip(p, result['box']))
            candidates = local_box_candidates(result['box'], 'ind')
            new = set(candidates['outer_candidates']); assert new <= old; old = new
            trajectory.append({'m': m, 'radius': str(result['radius']), 'candidates': sorted(new)})
        assert old == {'D01'}
        receipt['confidence_sequence_controls'] = {'integer_radius_checks': radius_checks,
                                                  'deterministic_count_fixture': trajectory,
                                                  'not_claimed': 'no empirical coverage experiment or biological data'}
        failed = 0
        for update in [(12000, [[6000, 4000, 2000]]), (13000, [[5999, 5001, 2000]]),
                       (13000, [[6000, 4000, 2000]])]:
            try: box_state.update(*update)
            except ValueError: failed += 1
            else: raise AssertionError('invalid cumulative prefix accepted')
        receipt['invalid_count_prefixes_rejected'] = failed
        un = local_box_candidates([(F(0), F(1))]*3, solver=lambda _: 'unknown')
        assert len(un['outer_candidates']) == 6 and len(un['unknown']) == 6
        receipt['all_unknown_local_guard'] = un
        request = {'taxa': ['a', 'b', 'c', 'd'],
                   'observations': [[['a', 'b', 'c', 'd'], ['2/3', '1/6', '1/6']]],
                   'closure': True, 'max_reticulations': 0}
        restricted = catalogue_request(request)
        assert restricted['catalogue_exhausted'] and not restricted['full_scope']
        assert restricted['all_class_outer_candidates'] == 'ALL_ADMITTED_TARGETS'
        interrupted = catalogue_request(dict(request, max_graphs=0, max_reticulations=5))
        assert not interrupted['catalogue_exhausted'] and interrupted['all_class_outer_candidates'] == 'ALL_ADMITTED_TARGETS'
        timed = bounded_request({'operation': 'solver', 'script': '(check-sat)'}, seconds=.000001)
        assert timed['reason'] == 'external_timeout'
        independent_worker = bounded_request({'operation': 'solver', 'script': '(set-logic QF_NRA)\n(assert false)\n(check-sat-using qfnra-nlsat)'}, seconds=5)
        assert independent_worker['status'] == 'unsat'
        receipt['global_guards'] = {'restricted_tree_census': restricted,
                                   'interrupted_full_bound': interrupted,
                                   'external_process_timeout': timed,
                                   'isolated_backend': independent_worker}
        taxa = ('a', 'b', 'c', 'd')
        splits = [frozenset([tuple(sorted((tuple(sorted(side)), tuple(sorted(set(taxa)-set(side))))))])
                  for side in [('a', 'b'), ('a', 'c'), ('a', 'd')]]
        out = project_target_set(taxa, splits)
        assert len(out['possible_orders']) == 3 and len(out['universally_valid_orders']) == 0
        assert not out['guaranteed_present'] and len(out['possibly_present']) == 3
        out2 = project_target_set(taxa, splits[:2])
        assert len(out2['universally_valid_orders']) == 1
        receipt['order_projection'] = {'three_candidate_targets': 3, 'possible_orders': 3,
                    'universally_valid_orders': 0, 'two_target_universally_valid_orders': 1,
                    'target_order_association_retained': True}

    receipt['environment'] = {'python': sys.version.split()[0], 'sympy': sp.__version__,
                             'networkx': nx.__version__, 'platform': platform.platform(),
                             'z3_library': ctypes.util.find_library('z3')}
    receipt['hashes'] = {str(path.relative_to(HERE)): hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in sorted(HERE.rglob('*.py'))}
    receipt['not_executed'] = ['full all-n source catalogue', 'whole-space all-n stratification',
                              'independent proof review', 'Lean formalization', 'biological experiment',
                              'full joint n-gene-law enumeration']
    (HERE/f'checks-{part}.json').write_text(json.dumps(receipt, indent=2)+'\n')
    if fixtures: (HERE/'solver-fixtures.json').write_text(json.dumps(fixtures, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'all')
