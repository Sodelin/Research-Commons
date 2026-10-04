"""Exact terminal G7 relation from admitted shared polynomial source models.

This is one remaining call, not recursive strategy synthesis. Completed QE and
NRA decisions have an explicit same-backend trust boundary. Partial work is
UNKNOWN. Quantified source names cannot capture free action names.
"""
import time
from collections import Counter
import sympy as sp
import z3


class EncodingError(ValueError):
    pass


def polynomial_to_z3(expression, symbols):
    expression = sp.sympify(expression)
    if expression.is_Rational:
        return z3.RealVal(str(expression))
    if expression.is_Symbol:
        if expression not in symbols:
            raise EncodingError('Unencoded polynomial symbol')
        return symbols[expression]
    if expression.is_Add:
        return sum((polynomial_to_z3(x, symbols) for x in expression.args), z3.RealVal(0))
    if expression.is_Mul:
        out = z3.RealVal(1)
        for x in expression.args:
            out *= polynomial_to_z3(x, symbols)
        return out
    if expression.is_Pow and expression.exp.is_Integer and expression.exp >= 0:
        return polynomial_to_z3(expression.base, symbols) ** int(expression.exp)
    raise EncodingError('Only exact rational polynomial laws are admitted')


def validate_models(models):
    if not models:
        raise EncodingError('A complete nonempty source catalogue is required')
    k, q = len(models[0]['laws']), len(models[0]['laws'][0])
    if k < 1 or q < 1:
        raise EncodingError('Empty law carrier')
    for model in models:
        variables = model['variables']
        if not all(isinstance(x, sp.Symbol) for x in variables) or len(set(variables)) != len(variables):
            raise EncodingError('Source variables must be distinct exact symbols')
        if len(model['laws']) != k or any(len(row) != q for row in model['laws']):
            raise EncodingError('Every source must have the same complete row and response carrier')
        for row in model['laws']:
            for value in row:
                if not value.free_symbols <= set(variables) or value.has(sp.Float):
                    raise EncodingError('Undeclared parameters or floating law coefficients')
                polynomial_to_z3(value, {x: z3.FreshReal('validation') for x in variables})
            if sp.expand(sum(row) - 1) != 0:
                raise EncodingError('Source row is not normalized')
    return k, q


def validate_history(history, k, q, supports):
    allowed = {tuple(sorted(s)) for s in supports}
    for weights, response in history:
        if len(weights) != k or len(response) != q:
            raise EncodingError('History has missing or extra row/response coordinates')
        if not all(x.is_Rational for x in weights + response):
            raise EncodingError('This history adapter currently admits exact rational histories only')
        if any(x < 0 for x in weights + response) or sum(weights) != 1 or sum(response) != 1:
            raise EncodingError('History vectors are not exact probability vectors')
        if tuple(i for i, x in enumerate(weights) if x > 0) not in allowed:
            raise EncodingError('Historical programme is outside the admitted support menu')


def source_pair(a, b, history, action=None):
    """Build from original parameter identities; one vector per competitor."""
    amap = {x: z3.FreshReal('sourceA') for x in a['variables']}
    bmap = {x: z3.FreshReal('sourceB') for x in b['variables']}
    constraints = [z3.And(v > 0, v < 1) for v in list(amap.values()) + list(bmap.values())]
    for model, symbols in ((a, amap), (b, bmap)):
        for weights, response in history:
            for coordinate, observed in enumerate(response):
                expression = sum(w * row[coordinate] for w, row in zip(weights, model['laws'])) - observed
                constraints.append(polynomial_to_z3(sp.expand(expression), symbols) == 0)
    if action is not None:
        for coordinate in range(len(a['laws'][0])):
            left = sum(action[i] * polynomial_to_z3(row[coordinate], amap) for i, row in enumerate(a['laws']))
            right = sum(action[i] * polynomial_to_z3(row[coordinate], bmap) for i, row in enumerate(b['laws']))
            constraints.append(left == right)
    return list(amap.values()) + list(bmap.values()), z3.And(*constraints)


def has_quantifier(expr):
    return z3.is_quantifier(expr) or any(has_quantifier(x) for x in expr.children())


def different_target_pairs(models):
    return [(i, j) for i in range(len(models)) for j in range(i + 1, len(models))
            if models[i]['target'] != models[j]['target']]


def different_target_pair_count(models):
    counts = Counter(model['target'] for model in models)
    return (len(models) ** 2 - sum(n ** 2 for n in counts.values())) // 2


def history_admitted(models, history, milliseconds):
    """Guard against vacuous identification of an impossible supplied history."""
    receipts = []; unknown = False
    for i, model in enumerate(models):
        _, formula = source_pair(model, model, history)
        solver = z3.SolverFor('QF_NRA'); solver.set(timeout=milliseconds); solver.add(formula)
        status = solver.check()
        receipts.append({'source_model': i, 'status': str(status), 'query_smt2': solver.to_smt2()})
        if status == z3.sat:
            return {'status': 'HISTORY_HAS_ADMITTED_SOURCE_SAME_BACKEND', 'receipts': receipts}
        if status != z3.unsat:
            unknown = True
    return {'status': 'UNKNOWN_HISTORY_SOURCE_ADMISSION' if unknown else 'NO_ADMITTED_SOURCE_FOR_HISTORY_SAME_BACKEND',
            'receipts': receipts}


def homogeneous_history(models, history, pairs, milliseconds):
    receipts = []
    for i, j in pairs:
        _, formula = source_pair(models[i], models[j], history)
        solver = z3.SolverFor('QF_NRA'); solver.set(timeout=milliseconds)
        solver.add(formula)
        status = solver.check()
        receipts.append({'pair': [i, j], 'status': str(status), 'query_smt2': solver.to_smt2()})
        if status == z3.sat:
            return {'status': 'HISTORY_NOT_HOMOGENEOUS', 'receipts': receipts}
        if status != z3.unsat:
            return {'status': 'UNKNOWN_HISTORY_HOMOGENEITY', 'reason': solver.reason_unknown(), 'receipts': receipts}
    return {'status': 'HISTORY_HOMOGENEOUS_SAME_BACKEND', 'receipts': receipts}


def final_call(models, history, support, pairs, milliseconds, encode_value):
    k = len(models[0]['laws'])
    weights = [z3.FreshReal('actionWeight') if i in support else z3.RealVal(0) for i in range(k)]
    legal = z3.And(*[weights[i] > 0 for i in support], sum(weights) == 1)
    relations = []; receipts = []
    for i, j in pairs:
        variables, collision = source_pair(models[i], models[j], history, weights)
        formula = z3.Exists(variables, z3.And(legal, collision)) if variables else z3.And(legal, collision)
        goal = z3.Goal(); goal.add(formula); start = time.monotonic()
        try:
            relation = z3.TryFor(z3.Tactic('qe'), milliseconds)(goal).as_expr()
        except z3.Z3Exception as exc:
            return {'status': 'UNKNOWN_QE_RESOURCE_LIMIT', 'reason': str(exc), 'receipts': receipts}
        receipts.append({'pair': [i, j], 'quantified_collision_smt2': formula.sexpr(),
                         'eliminated_relation_smt2': relation.sexpr(), 'elapsed_seconds': time.monotonic() - start})
        if has_quantifier(relation):
            return {'status': 'UNKNOWN_PARTIAL_SOURCE_PARAMETER_QE', 'receipts': receipts}
        relations.append(z3.Not(relation))
    winning = z3.And(legal, *relations)
    solver = z3.SolverFor('QF_NRA'); solver.set(timeout=milliseconds); solver.add(winning)
    status = solver.check()
    result = {'status': 'UNKNOWN_ACTION_DECISION', 'support_zero_based': support,
              'winning_relation_smt2': winning.sexpr(), 'action_query_smt2': solver.to_smt2(),
              'receipts': receipts, 'trust': 'exact symbolic source encoding plus completed Z3 QE/NRA; not independently proof-checked'}
    if status == z3.unsat:
        result['status'] = 'NO_TERMINAL_ACTION_FOR_SUPPORT_SAME_BACKEND'
    elif status == z3.sat:
        values = [solver.model().eval(w, model_completion=True) for w in weights]
        candidate = []
        for i, j in pairs:
            _, formula = source_pair(models[i], models[j], history, values)
            check = z3.SolverFor('QF_NRA'); check.set(timeout=milliseconds); check.add(formula)
            checked = check.check()
            candidate.append({'pair': [i, j], 'status': str(checked), 'query_smt2': check.to_smt2()})
            if checked != z3.unsat:
                result.update(status='UNKNOWN_CANDIDATE_RECHECK', candidate_receipts=candidate)
                return result
        result.update(status='TERMINAL_ACTION_RECOMPUTED_SAME_BACKEND',
                      weights=[encode_value(v) for v in values],
                      weights_smt2=[v.sexpr() for v in values], candidate_receipts=candidate)
    else:
        result['reason'] = solver.reason_unknown()
    return result
