"""Exact all-real-weight search within finite constant support skeletons.

This is a subset of adaptive G7 strategies. Failure/UNSAT here never supplies
NO for the full recursive budget. Real source assignments stay shared through
every planned call; the search is not a floating/rational weight grid.
"""
import itertools
import time
import z3
from recursive_engine import quantified
from selector_certificate import concrete_selector
from terminal_engine import has_quantifier


def search_constant_selector(engine, max_programs, max_skeletons=200, milliseconds=3000):
    checked = []; examined = 0
    for calls in range(1, max_programs + 1):
        for skeleton in itertools.product(engine.supports, repeat=calls):
            rows = set().union(*(set(s) for s in skeleton))
            sites = set().union(*(engine.row_sites[i] for i in rows))
            if len(rows) > engine.row_cap or len(sites) > engine.site_cap:
                continue
            examined += 1
            if examined > max_skeletons:
                return {'status': 'UNKNOWN_CONSTANT_SELECTOR_SKELETON_RESOURCE_LIMIT', 'checked': checked,
                        'adaptive_strategy_NO_claimed': False}
            variables = []; actions = []; legalities = []
            for support in skeleton:
                vv, weights, legal = engine.action(support)
                variables.extend(vv); actions.append(weights); legalities.append(legal)
            all_legal = z3.And(*legalities)
            collisions = []; pair_receipts = []; partial = False
            for i, j in engine.pairs:
                a, b = engine.models[i], engine.models[j]
                amap = {s: z3.FreshReal('constantSourceA') for s in a['variables']}
                bmap = {s: z3.FreshReal('constantSourceB') for s in b['variables']}
                alaws, ac = engine.consistency(a, amap, [])
                blaws, bc = engine.consistency(b, bmap, [])
                equations = [sum(w[r] * alaws[r][c] for r in range(engine.k))
                             == sum(w[r] * blaws[r][c] for r in range(engine.k))
                             for w in actions for c in range(engine.q)]
                raw = quantified(list(amap.values()) + list(bmap.values()),
                                 z3.And(*(ac + bc + equations + [all_legal])))
                goal = z3.Goal(); goal.add(raw); start = time.monotonic()
                try:
                    reduced = z3.TryFor(z3.Tactic('qe'), milliseconds)(goal).as_expr()
                except z3.Z3Exception:
                    reduced = raw
                pair_receipts.append({'source_pair': [i, j], 'raw_collision_smt2': raw.sexpr(),
                                      'reduced_collision_smt2': reduced.sexpr(),
                                      'elapsed_seconds': time.monotonic()-start})
                if has_quantifier(reduced):
                    partial = True; break
                collisions.append(reduced)
            record = {'support_skeleton': [list(s) for s in skeleton], 'pair_receipts': pair_receipts}
            if partial:
                record['status'] = 'UNKNOWN_CONSTANT_SELECTOR_SOURCE_QE'; checked.append(record); continue
            winning = z3.And(all_legal, *[z3.Not(c) for c in collisions])
            solver = z3.SolverFor('QF_NRA'); solver.set(timeout=milliseconds); solver.add(winning)
            answer = solver.check(); record['action_query_smt2'] = solver.to_smt2()
            record['status'] = str(answer); checked.append(record)
            if answer == z3.sat:
                concrete = [[solver.model().eval(w, model_completion=True) for w in action] for action in actions]
                certificate = concrete_selector(engine, concrete, max_programs, milliseconds)
                if certificate['status'] == 'CONCRETE_SELECTOR_AND_ACTUAL_SOURCE_DECODER_CERTIFIED_SAME_BACKEND':
                    return {'status': 'CONSTANT_SELECTOR_EXTRACTED_AND_CERTIFIED_SAME_BACKEND',
                            'checked': checked, 'selector_certificate': certificate,
                            'adaptive_selector_completeness_claimed': False}
                record['candidate_certificate'] = certificate
    return {'status': 'UNKNOWN_ADAPTIVE_SELECTOR_EXTRACTION_PENDING', 'checked': checked,
            'complete_constant_skeleton_search': not any(r['status'].startswith('UNKNOWN') or r['status'] == 'unknown'
                                                       for r in checked),
            'adaptive_strategy_NO_claimed': False}
