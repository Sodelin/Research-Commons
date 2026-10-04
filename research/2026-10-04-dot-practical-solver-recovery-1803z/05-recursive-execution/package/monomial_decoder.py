"""Sufficient exact decoder certificate for inherited CF source instances.

This uses the previously accepted ordinary-tree CF identity: a nonempty unit
monomial survival lies strictly between zero and one. It is not a generic CAD
selector algorithm and refuses conflicting target/coordinate associations.
"""
import sympy as sp
import z3


def certify(engine, weights, history_responses):
    if engine.q != 3 or len(history_responses) != 1:
        return None
    if not all(z3.is_rational_value(w) for w in weights):
        return None
    ww = [sp.Rational(str(w.as_fraction())) for w in weights]
    coordinate_target = {}; identities = []
    for index, model in enumerate(engine.models):
        law = [sp.expand(sum(w * row[c] for w, row in zip(ww, model['laws']))) for c in range(3)]
        admitted = None
        for own in range(3):
            off = [i for i in range(3) if i != own]
            survival = sp.expand(3 * law[off[0]])
            if sp.expand(law[off[0]] - law[off[1]]) != 0 or sp.expand(law[own] - (1 - 2*survival/3)) != 0:
                continue
            if not model['variables']:
                continue
            terms = sp.Poly(survival, *model['variables']).terms()
            if len(terms) != 1 or terms[0][1] != 1:
                continue
            exponents = terms[0][0]
            if not any(exponents) or any(type(p) is not int or p < 0 for p in exponents):
                continue
            admitted = (own, survival, exponents)
            break
        if admitted is None:
            return None
        own, survival, exponents = admitted
        if own in coordinate_target and coordinate_target[own] != model['target']:
            return None
        coordinate_target[own] = model['target']
        identities.append({'source_model': index, 'actual_target': model['target'],
                           'dominant_response_coordinate': own, 'survival_monomial': str(survival),
                           'original_parameter_exponents': {str(x): p for x, p in zip(model['variables'], exponents)},
                           'compiled_CF_identity': 'PASS_EXACT_RATIONAL_POLYNOMIAL_IDENTITY',
                           'strict_order_proof': 'Every original parameter is in (0,1); a nonempty unit monomial is in (0,1); own-minus-other equals 1-survival > 0'})
    y = history_responses[0]; targets = sorted(set(coordinate_target.values()), key=repr)
    regions = [{'target': target,
                'condition_smt2': z3.Or(*[z3.And(*[y[i] > y[j] for j in range(3) if j != i])
                                          for i, t in coordinate_target.items() if t == target]).sexpr()}
               for target in targets]
    return {'status': 'SUFFICIENT_ACTUAL_SOURCE_MONOMIAL_DECODER_CERTIFICATE',
            'response_variables': [[v.sexpr() for v in y]], 'target_regions': regions,
            'all_actual_source_polynomial_bindings': identities,
            'source_coverage': 'The caller must bind the complete actual original-source catalogue',
            'trust': 'Exact symbolic identity plus elementary strict monomial order; independent verifier remains a separate artifact',
            'generic_adaptive_CAD_claimed': False}
