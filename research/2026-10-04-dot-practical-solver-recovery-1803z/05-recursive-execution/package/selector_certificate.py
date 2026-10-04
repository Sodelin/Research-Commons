"""Certify concrete selectors and their actual-source target decoding regions.

Finite constant selectors are useful proof-backed extraction candidates. Failure
to find one is not evidence that no adaptive semialgebraic strategy exists.
Generic history-dependent CAD fibre selection remains a distinct gate.
"""
import z3
from recursive_engine import quantified, backend_decide


def concrete_selector(engine, programme_weights, max_programs, milliseconds=5000):
    if type(max_programs) is not int or max_programs < 0 or len(programme_weights) > max_programs:
        raise ValueError('Concrete selector exceeds the discrete programme PATH cap')
    used_rows = set(); used_sites = set(); path = []
    for weights in programme_weights:
        if len(weights) != engine.k:
            raise ValueError('Selector row carrier mismatch')
        if not all(z3.is_rational_value(w) or isinstance(w, z3.AlgebraicNumRef) for w in weights):
            raise ValueError('Concrete selector requires exact constant rational/algebraic weights')
        support = []
        for i, w in enumerate(weights):
            check = z3.SolverFor('QF_NRA'); check.add(w > 0)
            positive = check.check()
            zero = z3.SolverFor('QF_NRA'); zero.add(w == 0)
            if positive == z3.sat and zero.check() == z3.unsat:
                support.append(i)
            elif zero.check() != z3.sat or positive != z3.unsat:
                raise ValueError('Constant selector has a nonpositive or symbolic action')
        if support not in engine.supports:
            raise ValueError('Selector programme is outside the admitted support menu')
        normalized = z3.SolverFor('QF_NRA'); normalized.add(sum(weights) != 1)
        if normalized.check() != z3.unsat:
            raise ValueError('Selector weights are not normalized')
        used_rows |= set(support)
        used_sites |= set().union(*(engine.row_sites[i] for i in support))
        if len(used_rows) > engine.row_cap or len(used_sites) > engine.site_cap:
            raise ValueError('Selector exceeds cumulative PATH budgets')
        path.append({'call': len(path) + 1, 'support_zero_based': support,
                     'weights_smt2': [w.sexpr() for w in weights],
                     'cumulative_configurations': len(used_rows), 'cumulative_original_sites': len(used_sites)})
    receipt = backend_decide(z3.Not(engine.fixed_policy_counterexample(programme_weights)), milliseconds)
    if receipt['status'] != 'CLOSED_RECURSIVE_BUDGET_TRUE_SAME_BACKEND':
        return {'status': 'CONCRETE_SELECTOR_NOT_CERTIFIED', 'path': path, 'collision_check': receipt}

    responses = [[z3.FreshReal('selectorObservedResponse') for _ in range(engine.q)] for _ in programme_weights]
    # Reuse an existing accepted source-instance identity before generic CAD.
    # The complete source catalogue is checked, not a supplied output equality.
    if len(programme_weights) == 1:
        from monomial_decoder import certify
        structural = certify(engine, programme_weights[0], responses)
        if structural is not None:
            return {'status': 'CONCRETE_SELECTOR_AND_ACTUAL_SOURCE_DECODER_CERTIFIED_SAME_BACKEND',
                    'path': path, 'declared_path_budget': [max_programs, engine.row_cap, engine.site_cap],
                    'collision_check': receipt, 'response_variables': structural['response_variables'],
                    'target_regions': structural['target_regions'], 'structural_decoder_certificate': structural,
                    'generic_adaptive_CAD_selector_claimed': False,
                    'trust': 'Collision uses exact same-backend QE; decoder uses rederived actual-source CF identities and strict monomial order'}
    history = list(zip(programme_weights, responses))
    targets = sorted(set(m['target'] for m in engine.models), key=repr)
    regions = []; exact_predicates = []
    for target in targets:
        fibres = []
        for model in engine.models:
            if model['target'] != target:
                continue
            symbols = {s: z3.FreshReal('decoderOriginalParameter') for s in model['variables']}
            _, conditions = engine.consistency(model, symbols, history)
            fibres.append(quantified(list(symbols.values()), z3.And(*conditions)))
        predicate = z3.Or(*fibres); exact_predicates.append(predicate)
        result = backend_decide(predicate, milliseconds, return_ast=True)
        reduced = result.pop('_formula_ast', None)
        if result['status'] not in ('FREE_SYMBOLIC_HISTORY_RELATION_SAME_BACKEND',
                                    'CLOSED_RECURSIVE_BUDGET_TRUE_SAME_BACKEND',
                                    'CLOSED_RECURSIVE_BUDGET_FALSE_SAME_BACKEND'):
            return {'status': 'UNKNOWN_SELECTOR_TARGET_REGION_QE', 'path': path,
                    'collision_check': receipt, 'completed_regions': regions, 'partial_region': result}
        # Keep the SAME checked AST for source substitution; do not parse supplied SMT.
        regions.append({'target': target, 'formula': reduced, 'receipt': result})

    # Certify total and correct target guards on EVERY actual admitted source.
    source_checks = []
    flattened_response = [x for block in responses for x in block]
    for index, model in enumerate(engine.models):
        symbols = {s: z3.FreshReal('selectorActualSource') for s in model['variables']}
        laws, domain = engine.consistency(model, symbols, [])
        observed = [sum(weights[i] * laws[i][c] for i in range(engine.k))
                    for weights in programme_weights for c in range(engine.q)]
        subst = list(zip(flattened_response, observed))
        truth = [z3.substitute(r['formula'], *subst) if r['target'] == model['target']
                 else z3.Not(z3.substitute(r['formula'], *subst)) for r in regions]
        formula = quantified(list(symbols.values()), z3.Implies(z3.And(*domain), z3.And(*truth)), universal=True)
        checked = backend_decide(formula, milliseconds)
        source_checks.append({'source_model': index, 'actual_target': model['target'], 'check': checked})
        if checked['status'] != 'CLOSED_RECURSIVE_BUDGET_TRUE_SAME_BACKEND':
            return {'status': 'UNKNOWN_OR_FAILED_ACTUAL_SOURCE_SELECTOR_DECODER', 'path': path,
                    'collision_check': receipt, 'source_checks': source_checks}
    return {'status': 'CONCRETE_SELECTOR_AND_ACTUAL_SOURCE_DECODER_CERTIFIED_SAME_BACKEND',
            'path': path, 'collision_check': receipt,
            'declared_path_budget': [max_programs, engine.row_cap, engine.site_cap],
            'response_variables': [[v.sexpr() for v in block] for block in responses],
            'target_regions': [{'target': r['target'], 'condition_smt2': r['formula'].sexpr(), 'qe_receipt': r['receipt']}
                               for r in regions], 'all_actual_source_decoder_checks': source_checks,
            'generic_adaptive_CAD_selector_claimed': False,
            'trust': 'Complete same-backend symbolic collision, region QE and all-original-source decoder checks'}
