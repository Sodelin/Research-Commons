#!/usr/bin/env python3
"""Recompile actual sources and recheck a terminal action, never supplied SMT.

This is a fresh exact same-backend NRA check, not an independent proof checker.
The 33-pair positive-identity experiment has a separate independent verifier.
"""
import argparse
from fractions import Fraction
from math import lcm
import hashlib
import json
from pathlib import Path
import tempfile
import sympy as sp
import z3
from terminal_g7 import (prepare, verify_base, parse_polynomial, require, export,
                         InvalidInput, Unsupported)
from terminal_engine import (validate_models, validate_history, source_pair,
                             different_target_pairs, history_admitted, homogeneous_history,
                             final_call)
from solver import encode_value


def exact_weight(record):
    if record.get('kind') == 'rational' and set(record) == {'kind', 'value'}:
        require(isinstance(record['value'], str), 'Exact rational weight requires a string')
        return z3.RealVal(str(Fraction(record['value'])))
    require(record.get('kind') == 'algebraic' and set(record) == {'kind', 'polynomial_ascending', 'real_root_index'},
            'Unknown exact real weight encoding')
    coefficients = record['polynomial_ascending']; index = record['real_root_index']
    require(isinstance(coefficients, list) and len(coefficients) >= 2,
            'Invalid algebraic polynomial degree')
    require(type(index) is int and index >= 1, 'Invalid algebraic root index')
    require(all(isinstance(c, str) for c in coefficients), 'Algebraic coefficients require exact strings')
    rational_coefficients = [Fraction(c) for c in coefficients]
    require(rational_coefficients[-1] != 0, 'Algebraic defining polynomial has zero leading coefficient')
    # root-obj expects integer polynomial coefficients; positive denominator
    # clearing preserves every real root and its ordering exactly.
    denominator = lcm(*(c.denominator for c in rational_coefficients))
    integer_coefficients = [int(c * denominator) for c in rational_coefficients]
    terms = ['(* ' + z3.IntVal(c).sexpr() + ' (^ x ' + str(i) + '))'
             for i, c in enumerate(integer_coefficients) if c]
    polynomial = '(+ ' + ' '.join(terms) + ')' if len(terms) > 1 else terms[0]
    # The text contains only reconstructed integer/rational arithmetic, no supplied SMT.
    parsed = z3.parse_smt2_string('(declare-fun certWeight () Real) (assert (= certWeight (root-obj '
                                 + polynomial + ' ' + str(index) + ')))')
    require(len(parsed) == 1 and z3.is_eq(parsed[0]), 'Invalid algebraic root constant')
    value = parsed[0].arg(1)
    require(isinstance(value, z3.AlgebraicNumRef), 'Expected an irrational real algebraic constant')
    return value


def verify(path):
    result = json.loads(Path(path).read_text())
    require(result.get('schema') == 'actual-source-terminal-G7-result-v1', 'Wrong result schema')
    for scope in ['full_recursive_policy_synthesis_claimed', 'Lean_certification_claimed',
                  'empirical_admission_claimed', 'unknown_size_termination_or_global_NO_claimed']:
        require(result.get(scope) is False, 'Unsupported scope claim')
    require(result['base_manifest_sha256'] == verify_base(), 'Wrong inherited source pin')
    design, history, budget, supports, ids, milliseconds, max_pairs = prepare(result['request'])
    with tempfile.TemporaryDirectory(prefix='terminal-source-recheck-') as tmp:
        report = export(design, tmp)
        require(report.get('catalogue_exhausted') is True, 'Actual source recompilation is incomplete')
        provider_path = Path(tmp) / 'ACTUAL-SOURCE-MODELS.json'
        require(hashlib.sha256(provider_path.read_bytes()).hexdigest() == result['actual_source_models_sha256'],
                'Delivered provider differs from the freshly recompiled complete actual source catalogue')
        provider = json.loads(provider_path.read_text())
    models = []
    for record in provider['models']:
        variables = {name: sp.Symbol(name) for name in record['variable_mapping'].values()}
        models.append({'variables': list(variables.values()),
                       'laws': [[parse_polynomial(p, variables) for p in row] for row in record['laws']],
                       'target': record['target_code']})
    k, q = validate_models(models); validate_history(history, k, q, supports)
    require(result['actual_source_count'] == provider['source_count_examined']
            and result['actual_source_mode_models'] == len(models)
            and result['target_kind'] == provider['target_kind']
            and result['response_coordinates'] == q, 'Actual source scope/count/target mismatch')
    pairs = different_target_pairs(models)
    require(len(pairs) <= max_pairs and result['different_target_pairs'] == len(pairs), 'Incomplete pair carrier')
    used_rows = {i for weights, _ in history for i, w in enumerate(weights) if w > 0}
    row_sites = [set(op) for op in design['deterministic_rows']]
    used_sites = set().union(*(row_sites[i] for i in used_rows))
    require(len(history) <= budget[0] and len(used_rows) <= budget[1] and len(used_sites) <= budget[2],
            'Delivered historical path already exceeds the declared budgets')
    status = result['status']
    admission = history_admitted(models, history, milliseconds)
    if status == 'NO_ADMITTED_SOURCE_FOR_HISTORY_SAME_BACKEND':
        require(admission['status'] == status, 'Impossible-history claim did not replay')
        return {'status': 'PASS_ACTUAL_SOURCE_IMPOSSIBLE_HISTORY_REPLAY', 'trust': 'fresh same-backend NRA'}
    require(admission['status'] == 'HISTORY_HAS_ADMITTED_SOURCE_SAME_BACKEND', 'History admission is not complete')
    if status == 'NO_ADDITIONAL_CALL_NEEDED_SAME_BACKEND':
        require(homogeneous_history(models, history, pairs, milliseconds)['status'] == 'HISTORY_HOMOGENEOUS_SAME_BACKEND',
                'Zero-call identification claim did not replay')
        return {'status': 'PASS_ACTUAL_SOURCE_HISTORY_HOMOGENEITY_REPLAY', 'trust': 'fresh same-backend NRA'}
    if status == 'TERMINAL_ACTION_RECOMPUTED_SAME_BACKEND':
        index = result['chosen_action_index']
        require(type(index) is int and 0 <= index < len(result['actions']), 'Invalid chosen-action index')
        action = result['actions'][index]
        support = action['support_zero_based']
        require(support in supports, 'Chosen support is not in the original legal menu')
        weights = [exact_weight(v) for v in action['weights']]
        require(len(weights) == k, 'Action vector has wrong carrier')
        legal = z3.And(*[weights[i] > 0 if i in support else weights[i] == 0 for i in range(k)], sum(weights) == 1)
        check = z3.SolverFor('QF_NRA'); check.add(z3.Not(legal))
        require(check.check() == z3.unsat, 'Exact real action is outside its positive simplex')
        rows = used_rows | set(support); sites = set().union(*(row_sites[i] for i in rows))
        require(len(history) + 1 <= budget[0] and len(rows) <= budget[1] and len(sites) <= budget[2],
                'Chosen programme exceeds the exact PATH budgets')
        for i, j in pairs:
            _, formula = source_pair(models[i], models[j], history, weights)
            solver = z3.SolverFor('QF_NRA'); solver.set(timeout=milliseconds); solver.add(formula)
            require(solver.check() == z3.unsat, 'Actual-source equal-response collision was not excluded')
        return {'status': 'PASS_FRESH_ACTUAL_SOURCE_TERMINAL_ACTION_REPLAY', 'source_count': provider['source_count_examined'],
                'different_target_pairs': len(pairs), 'exact_weight_kinds': [v['kind'] for v in action['weights']],
                'supplied_SMT_or_QE_output_trusted': False, 'trust': 'fresh exact same-backend NRA from recompiled source rows'}
    require(status == 'NO_TERMINAL_EXTENSION_WITHIN_PATH_BUDGET_SAME_BACKEND', 'No terminal verdict is claimed')
    require(homogeneous_history(models, history, pairs, milliseconds)['status'] == 'HISTORY_NOT_HOMOGENEOUS',
            'History is not proven to need another call')
    if len(history) + 1 <= budget[0]:
        for support in supports:
            rows = used_rows | set(support); sites = set().union(*(row_sites[i] for i in rows))
            if len(rows) > budget[1] or len(sites) > budget[2]:
                continue
            require(final_call(models, history, support, pairs, milliseconds, encode_value)['status']
                    == 'NO_TERMINAL_ACTION_FOR_SUPPORT_SAME_BACKEND', 'A legal terminal support is not excluded')
    return {'status': 'PASS_ACTUAL_SOURCE_BOUNDED_TERMINAL_NO_REPLAY', 'trust': 'fresh same-backend QE/NRA',
            'global_unknown_size_NO_claimed': False}


def main():
    ap = argparse.ArgumentParser(description=__doc__); ap.add_argument('result'); args = ap.parse_args()
    print(json.dumps(verify(args.result), indent=2))


if __name__ == '__main__':
    main()
