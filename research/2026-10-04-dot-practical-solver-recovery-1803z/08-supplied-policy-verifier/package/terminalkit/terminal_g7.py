#!/usr/bin/env python3
"""Actual source admission -> one-remaining-call G7 relation/action.

Known complete original registry, inherited exact source compiler and legal
finite action menu. General recursive strategy synthesis remains pending.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as sp
import z3

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'sourcekit'))
from solver import InvalidInput, Unsupported, rational, encode_value, identity
from export_design import export, validated
from terminal_engine import (EncodingError, validate_models, validate_history,
                             different_target_pairs, different_target_pair_count,
                             history_admitted, homogeneous_history, final_call)


def require(value, message):
    if not value:
        raise InvalidInput(message)


def verify_base():
    binding = json.loads((ROOT / 'BASE-BINDING.json').read_text())
    for record in binding['files']:
        data = (ROOT / record['path']).read_bytes()
        require(len(data) == record['bytes'] and hashlib.sha256(data).hexdigest() == record['sha256'],
                'Reviewed base source bytes changed')
    identity()
    return binding['base_manifest_sha256']


def parse_polynomial(text, variables):
    """Safe rational-polynomial parser; no Python/SymPy evaluation of input."""
    def go(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return sp.Integer(node.value)
        if isinstance(node, ast.Name) and node.id in variables:
            return variables[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -go(node.operand)
        if isinstance(node, ast.BinOp):
            a, b = go(node.left), go(node.right)
            if isinstance(node.op, ast.Add): return a + b
            if isinstance(node.op, ast.Sub): return a - b
            if isinstance(node.op, ast.Mult): return a * b
            if isinstance(node.op, ast.Div) and b.is_Rational and b != 0: return a / b
            if isinstance(node.op, ast.Pow) and b.is_Integer and b >= 0: return a ** b
        raise InvalidInput('Unencoded source polynomial syntax')
    return sp.expand(go(ast.parse(text, mode='eval').body))


def prepare(request):
    require(isinstance(request, dict), 'Request must be an object')
    require(set(request) <= {'schema', 'design_request', 'history', 'budget', 'backend_limits'},
            'Unsupported terminal request fields')
    require(request.get('schema') == 'actual-source-terminal-G7-request-v1', 'Wrong terminal schema')
    design = request['design_request']
    n, ids, modes, samples, readout, target, forces, supports, budgets, limits = validated(design)
    budget = request['budget']
    require(isinstance(budget, list) and len(budget) == 3 and all(type(x) is int and x >= 0 for x in budget),
            'Budget must be three nonnegative integer PATH caps')
    require(budget in budgets, 'Requested terminal budget is not declared in the source design')
    supports = [sorted(i - 1 for i in support) for support in supports]
    histories = request.get('history', [])
    require(isinstance(histories, list), 'History must be a finite list')
    history = []
    for old in histories:
        require(isinstance(old, dict) and set(old) == {'row_weights', 'response'}, 'Unknown history fields')
        require(isinstance(old['row_weights'], list) and isinstance(old['response'], list), 'History vectors must be lists')
        # rational() rejects floats; exact algebraic/symbolic histories need a separate encoder.
        history.append(([rational(x) for x in old['row_weights']], [rational(x) for x in old['response']]))
    backend = request.get('backend_limits', {})
    require(isinstance(backend, dict) and set(backend) <= {'per_pair_ms', 'max_pairs'}, 'Unknown backend limits')
    milliseconds = backend.get('per_pair_ms', 3000)
    max_pairs = backend.get('max_pairs', 500)
    require(type(milliseconds) is int and 1 <= milliseconds <= 60000, 'Invalid per-pair limit')
    require(type(max_pairs) is int and 1 <= max_pairs <= 100000, 'Invalid pair limit')
    return design, history, budget, supports, ids, milliseconds, max_pairs


def run(request, directory):
    directory = Path(directory); directory.mkdir(parents=True, exist_ok=True)
    started = time.monotonic(); base_pin = verify_base()
    design, history, budget, supports, ids, milliseconds, max_pairs = prepare(request)
    exported = export(design, directory / 'source-export')
    if not exported.get('catalogue_exhausted'):
        return {'status': 'UNKNOWN_INCOMPLETE_ACTUAL_SOURCE_EXPORT', 'export': exported}
    model_path = directory / 'source-export/ACTUAL-SOURCE-MODELS.json'
    provider = json.loads(model_path.read_text())
    models = []
    for record in provider['models']:
        variables = {name: sp.Symbol(name) for name in record['variable_mapping'].values()}
        models.append({'variables': list(variables.values()),
                       'laws': [[parse_polynomial(p, variables) for p in row] for row in record['laws']],
                       'target': record['target_code']})
    k, q = validate_models(models); validate_history(history, k, q, supports)
    used_rows = {i for weights, _ in history for i, w in enumerate(weights) if w > 0}
    row_sites = [set(operation) for operation in design['deterministic_rows']]
    used_sites = set().union(*(row_sites[i] for i in used_rows))
    require(len(history) <= budget[0] and len(used_rows) <= budget[1] and len(used_sites) <= budget[2],
            'Historical programme path already exceeds the declared budget')
    report = {'schema': 'actual-source-terminal-G7-result-v1', 'status': 'UNKNOWN_TERMINAL_DECISION',
              'request': request, 'base_manifest_sha256': base_pin,
              'actual_source_models_sha256': hashlib.sha256(model_path.read_bytes()).hexdigest(),
              'catalogue_exhausted': True, 'actual_source_count': provider['source_count_examined'],
              'actual_source_mode_models': len(models), 'response_coordinates': q,
              'target_kind': provider['target_kind'], 'software': {'sympy': sp.__version__, 'z3': z3.get_version_string()},
              'used_rows_zero_based': sorted(used_rows), 'used_original_sites': sorted(used_sites),
              'scope': 'One remaining exact pooled-law call after a supplied exact rational history, complete known original registry and inherited legal reset/deletion-closed PATH budgets',
              'full_recursive_policy_synthesis_claimed': False, 'Lean_certification_claimed': False,
              'empirical_admission_claimed': False, 'unknown_size_termination_or_global_NO_claimed': False}
    pair_count = different_target_pair_count(models)
    report['different_target_pairs'] = pair_count
    if pair_count > max_pairs:
        report.update(status='UNKNOWN_SOURCE_PAIR_RESOURCE_LIMIT', max_pairs=max_pairs)
        return report
    pairs = different_target_pairs(models)
    admission = history_admitted(models, history, milliseconds)
    report['history_source_admission'] = admission
    if admission['status'] != 'HISTORY_HAS_ADMITTED_SOURCE_SAME_BACKEND':
        report['status'] = admission['status']; return report
    homogeneous = homogeneous_history(models, history, pairs, milliseconds)
    report['history_homogeneity'] = homogeneous
    if homogeneous['status'] == 'HISTORY_HOMOGENEOUS_SAME_BACKEND':
        report['status'] = 'NO_ADDITIONAL_CALL_NEEDED_SAME_BACKEND'
        return report
    if homogeneous['status'].startswith('UNKNOWN'):
        report['status'] = homogeneous['status']; return report
    if len(history) + 1 > budget[0]:
        report['status'] = 'NO_TERMINAL_EXTENSION_WITHIN_PATH_BUDGET_SAME_BACKEND'; return report
    actions = []
    for support in supports:
        rows = used_rows | set(support)
        sites = set().union(*(row_sites[i] for i in rows))
        if len(rows) > budget[1] or len(sites) > budget[2]:
            continue
        action = final_call(models, history, support, pairs, milliseconds, encode_value)
        action['path_budget_after_call'] = [len(history) + 1, len(rows), len(sites)]
        actions.append(action)
        if action['status'] == 'TERMINAL_ACTION_RECOMPUTED_SAME_BACKEND':
            report.update(status=action['status'], chosen_action_index=len(actions) - 1)
            break
    if report['status'] == 'UNKNOWN_TERMINAL_DECISION':
        report['status'] = ('UNKNOWN_TERMINAL_BACKEND' if any(a['status'].startswith('UNKNOWN') for a in actions)
                            else 'NO_TERMINAL_EXTENSION_WITHIN_PATH_BUDGET_SAME_BACKEND')
    report.update(actions=actions, elapsed_seconds=time.monotonic() - started,
                  trust='The actual source catalogue/laws are compiled here; completed symbolic QE and exact NRA decisions/candidate rechecks use Z3 and are not independently proof-checked')
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('request'); ap.add_argument('--output', required=True)
    args = ap.parse_args()
    request = json.loads(Path(args.request).read_text())
    try:
        result = run(request, args.output)
    except (InvalidInput, Unsupported, EncodingError, KeyError, TypeError, ValueError, SyntaxError) as exc:
        result = {'schema': 'actual-source-terminal-G7-result-v1', 'status': 'REJECTED_TERMINAL_ENCODING',
                  'reason': str(exc), 'empirical_admission_claimed': False,
                  'full_recursive_policy_synthesis_claimed': False}
    directory = Path(args.output); directory.mkdir(parents=True, exist_ok=True)
    (directory / 'TERMINAL-RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'actual_source_count', 'actual_source_mode_models',
                                           'different_target_pairs', 'elapsed_seconds', 'reason') if k in result}, indent=2))
    return 0 if result['status'] in ('TERMINAL_ACTION_RECOMPUTED_SAME_BACKEND',
                                   'NO_ADDITIONAL_CALL_NEEDED_SAME_BACKEND',
                                   'NO_ADMITTED_SOURCE_FOR_HISTORY_SAME_BACKEND',
                                   'NO_TERMINAL_EXTENSION_WITHIN_PATH_BUDGET_SAME_BACKEND') else 2


if __name__ == '__main__':
    raise SystemExit(main())
