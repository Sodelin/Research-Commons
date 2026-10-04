#!/usr/bin/env python3
"""Meaningful actual-source, history, budget and certificate-boundary controls."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as sp
import z3
from terminal_g7 import run, prepare, parse_polynomial, InvalidInput, Unsupported, ROOT
from terminal_engine import (EncodingError, validate_models, validate_history,
                             different_target_pairs, homogeneous_history, final_call)
from verify_terminal_result import verify, exact_weight
from solver import encode_value


def require(value, message):
    if not value:
        raise RuntimeError(message)


def main():
    start = time.monotonic()
    baseline = json.loads((ROOT / 'examples/actual-source-terminal.json').read_text())
    cases = [('actual-source-terminal', baseline, 'TERMINAL_ACTION_RECOMPUTED_SAME_BACKEND')]
    no_budget = copy.deepcopy(baseline); no_budget['budget'] = [0, 0, 0]
    cases.append(('zero-call-budget', no_budget, 'NO_TERMINAL_EXTENSION_WITHIN_PATH_BUDGET_SAME_BACKEND'))
    known = copy.deepcopy(baseline); known['history'] = [{'row_weights': ['1'], 'response': ['2/3', '1/6', '1/6']}]
    cases.append(('existing-target-history', known, 'NO_ADDITIONAL_CALL_NEEDED_SAME_BACKEND'))
    impossible = copy.deepcopy(baseline); impossible['history'] = [{'row_weights': ['1'], 'response': ['1/3', '1/3', '1/3']}]
    cases.append(('impossible-history', impossible, 'NO_ADMITTED_SOURCE_FOR_HISTORY_SAME_BACKEND'))
    limited = copy.deepcopy(baseline); limited['backend_limits']['max_pairs'] = 1
    cases.append(('pair-limit', limited, 'UNKNOWN_SOURCE_PAIR_RESOURCE_LIMIT'))
    receipts = []
    for name, request, expected in cases:
        directory = ROOT / 'runs' / name; directory.mkdir(parents=True, exist_ok=True)
        (ROOT / 'examples' / (name + '.json')).write_text(json.dumps(request, indent=2) + '\n')
        result = run(request, directory)
        require(result['status'] == expected, name + ': wrong terminal status ' + result['status'])
        file = directory / 'TERMINAL-RESULT.json'; file.write_text(json.dumps(result, indent=2) + '\n')
        recheck = None if expected.startswith('UNKNOWN') else verify(file)
        receipts.append({'case': name, 'status': result['status'], 'result_sha256': hashlib.sha256(file.read_bytes()).hexdigest(),
                         'fresh_actual_source_recheck': recheck})

    # Abstract control only: SAME parameter across old/new rows is indispensable.
    x = sp.Symbol('originalSourceParameter')
    models = [{'variables': [x], 'laws': [[x, 1-x], [x, 1-x]], 'target': 0},
              {'variables': [x], 'laws': [[x, 1-x], [1-x, x]], 'target': 1}]
    history = [([sp.Integer(1), sp.Integer(0)], [sp.Rational(1, 4), sp.Rational(3, 4)])]
    k, q = validate_models(models); validate_history(history, k, q, [[0], [1]])
    pairs = different_target_pairs(models)
    require(homogeneous_history(models, history, pairs, 3000)['status'] == 'HISTORY_NOT_HOMOGENEOUS',
            'Shared-parameter control should still be ambiguous before the second row')
    control = final_call(models, history, [1], pairs, 3000, encode_value)
    require(control['status'] == 'TERMINAL_ACTION_RECOMPUTED_SAME_BACKEND',
            'Shared historical parameters were not retained in the proposed row')

    guards = []
    bad = copy.deepcopy(baseline); bad['design_request']['empirical_admission'] = {'status': 'ADMITTED'}; guards.append(('empirical-payload', bad))
    bad = copy.deepcopy(baseline); bad['history'] = [{'row_weights': [1.0], 'response': ['2/3', '1/6', '1/6']}]; guards.append(('floating-history', bad))
    bad = copy.deepcopy(baseline); bad['extra_observation_constraint'] = 'unencoded'; guards.append(('unencoded-constraint', bad))
    for name, bad in guards:
        try:
            prepare(bad)
        except (InvalidInput, Unsupported):
            continue
        raise RuntimeError('Unsupported contract accepted: ' + name)
    try:
        validate_history([([sp.Integer(1)], [sp.Integer(1)])], 1, 3, [[0]])
    except EncodingError:
        pass
    else:
        raise RuntimeError('Missing response coordinates were silently truncated')

    # Exact algebraic real actions are supported; no rational-only policy claim.
    w = z3.Real('algebraicWeight'); solve = z3.SolverFor('QF_NRA'); solve.add(2*w*w == 1, w > 0)
    require(solve.check() == z3.sat, 'Algebraic encoding control failed')
    encoded = encode_value(solve.model()[w]); decoded = exact_weight(encoded)
    check = z3.SolverFor('QF_NRA'); check.add(z3.Or(decoded <= 0, decoded >= 1, 2*decoded*decoded != 1))
    require(check.check() == z3.unsat, 'Algebraic weight was not reconstructed exactly')
    require(parse_polynomial('parameter**101', {'parameter': x}) == x ** 101,
            'An artificial written-exponent cap remains')
    high_degree = {'kind': 'algebraic', 'polynomial_ascending': ['-1/2'] + ['0'] * 100 + ['1'],
                   'real_root_index': 1}
    require(isinstance(exact_weight(high_degree), z3.AlgebraicNumRef),
            'An artificial algebraic defining-polynomial degree cap remains')

    # Delivered formula text cannot substitute for freshly derived source rows.
    sample = json.loads((ROOT / 'runs/actual-source-terminal/TERMINAL-RESULT.json').read_text())
    sample['actions'][0]['winning_relation_smt2'] = 'false'
    file = ROOT / 'runs/unused-formula-control.json'; file.write_text(json.dumps(sample, indent=2)+'\n')
    require(verify(file)['status'] == 'PASS_FRESH_ACTUAL_SOURCE_TERMINAL_ACTION_REPLAY',
            'Recheck improperly trusted supplied QE/formula text')
    sample['actions'][0]['weights'] = [{'kind': 'rational', 'value': '0'}]
    file = ROOT / 'runs/tampered-weight-control.json'; file.write_text(json.dumps(sample, indent=2)+'\n')
    try:
        verify(file)
    except InvalidInput:
        pass
    else:
        raise RuntimeError('An illegal delivered action was accepted')
    receipt = {'schema': 'actual-source-terminal-integration-test-v1', 'status': 'PASS',
               'actual_source_workflow_cases': receipts, 'shared_parameter_history_control': 'PASS_ABSTRACT_IMPLEMENTATION_CONTROL',
               'unsupported_contract_rejections': [name for name, _ in guards] + ['missing-response-coordinate'],
               'exact_algebraic_weight_reconstruction': 'PASS', 'supplied_formula_not_trusted': 'PASS',
               'finite_integer_power_and_algebraic_degree_encoding': 'PASS_WITHOUT_ARTIFICIAL_DEGREE_CAPS',
               'tampered_action_rejected': 'PASS', 'python': sys.version.split()[0], 'sympy': sp.__version__,
               'z3': z3.get_version_string(), 'elapsed_seconds': time.monotonic()-start,
               'trust': 'Actual sources are freshly compiled; generic mathematical decisions use completed same-backend Z3 checks, not independent/Lean proof certificates',
               'full_recursive_G7_claimed': False}
    (ROOT / 'TEST-RECEIPT.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('status','exact_algebraic_weight_reconstruction','tampered_action_rejected','elapsed_seconds')}, indent=2))


if __name__ == '__main__':
    main()
