#!/usr/bin/env python3
"""Actual finite source export -> ordered recursive G7 budget and selector.

Exact symbolic histories are generated through every response quantifier.
Concrete supplied histories admit rational/algebraic real values. A completed
budget Boolean and a certified selector are reported as different outcomes.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as sp
import z3

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'terminalkit'))
from terminal_g7 import verify_base, parse_polynomial, require, InvalidInput, Unsupported
from verify_terminal_result import exact_weight
from export_design import export, validated
from solver import rational
from terminal_engine import validate_models
from recursive_engine import WinningFormula, FormulaLimit, at_most_budget_decide, quantified
from constant_selector_search import search_constant_selector


def exact_value(value):
    if isinstance(value, dict):
        return exact_weight(value)
    return z3.RealVal(str(rational(value)))


def probability_vector(data, length):
    require(isinstance(data, list) and len(data) == length, 'Missing or extra probability coordinates')
    values = [exact_value(x) for x in data]
    check = z3.SolverFor('QF_NRA')
    check.add(z3.Not(z3.And(*[x >= 0 for x in values], sum(values) == 1)))
    require(check.check() == z3.unsat, 'Exact history vector is not a probability vector')
    return values


def positive_support(values):
    return [i for i, x in enumerate(values) if z3.is_true(z3.simplify(x > 0))]


def initial_history_admission(engine, history, milliseconds):
    reports = []; unknown = False
    for i, model in enumerate(engine.models):
        symbols = {s: z3.FreshReal('historyOriginalParameter') for s in model['variables']}
        _, constraints = engine.consistency(model, symbols, history)
        check = z3.SolverFor('QF_NRA'); check.set(timeout=milliseconds); check.add(*constraints)
        status = check.check(); reports.append({'source_model': i, 'status': str(status), 'query_smt2': check.to_smt2()})
        if status == z3.sat:
            return {'status': 'ACTUAL_HISTORY_ADMITTED_SAME_BACKEND', 'receipts': reports}
        if status != z3.unsat:
            unknown = True
    return {'status': 'UNKNOWN_HISTORY_ADMISSION' if unknown else 'NO_ACTUAL_SOURCE_FOR_HISTORY_SAME_BACKEND',
            'receipts': reports}


def run(request, directory):
    started = time.monotonic(); directory = Path(directory); directory.mkdir(parents=True, exist_ok=True)
    binding = json.loads((ROOT / 'TERMINAL-BASE-BINDING.json').read_text())
    for entry in binding['files']:
        require(hashlib.sha256((ROOT / entry['path']).read_bytes()).hexdigest() == entry['sha256'],
                'Reviewed terminal source binding changed')
    verify_base()
    require(isinstance(request, dict) and set(request) <= {'schema', 'design_request', 'history', 'budget', 'backend_limits'},
            'Unsupported recursive input fields')
    require(request.get('schema') == 'actual-source-recursive-G7-request-v1', 'Wrong recursive request schema')
    design = request['design_request']
    n, ids, modes, samples, readout, target, forces, supports, budgets, limits = validated(design)
    budget = request['budget']; require(budget in budgets, 'Budget not declared in the actual source design')
    supports = [sorted(i-1 for i in support) for support in supports]
    backend = request.get('backend_limits', {})
    require(isinstance(backend, dict) and set(backend) <= {'per_qe_ms', 'max_pairs', 'max_formula_nodes', 'max_selector_skeletons'},
            'Unknown recursive backend limits')
    ms = backend.get('per_qe_ms', 3000); pair_cap = backend.get('max_pairs', 500)
    node_cap = backend.get('max_formula_nodes', 10000); selector_cap = backend.get('max_selector_skeletons', 100)
    require(all(type(v) is int and v > 0 for v in (ms, pair_cap, node_cap, selector_cap)), 'Positive integer limits required')
    require(ms <= 60000, 'Per-QE timeout exceeds 60 seconds')
    exported = export(design, directory / 'source-export')
    if not exported.get('catalogue_exhausted'):
        return {'status': 'UNKNOWN_INCOMPLETE_ACTUAL_SOURCE_EXPORT', 'export': exported}
    provider_path = directory / 'source-export/ACTUAL-SOURCE-MODELS.json'
    provider = json.loads(provider_path.read_text()); models = []
    for record in provider['models']:
        variables = {name: sp.Symbol(name) for name in record['variable_mapping'].values()}
        models.append({'variables': list(variables.values()),
                       'laws': [[parse_polynomial(p, variables) for p in row] for row in record['laws']],
                       'target': record['target_code']})
    k, q = validate_models(models)
    history = []; old_rows = set(); old_sites = set()
    row_sites = [set(op) for op in design['deterministic_rows']]
    for old in request.get('history', []):
        require(isinstance(old, dict) and set(old) == {'row_weights', 'response'}, 'Unknown history fields')
        weights = probability_vector(old['row_weights'], k); response = probability_vector(old['response'], q)
        support = positive_support(weights); require(support in supports, 'Historical action is not in the original menu')
        history.append((weights, response)); old_rows |= set(support)
        old_sites |= set().union(*(row_sites[i] for i in support))
    require(len(history) <= budget[0] and len(old_rows) <= budget[1] and len(old_sites) <= budget[2],
            'The historical PATH already exceeds its programme/configuration/site caps')
    report = {'schema': 'actual-source-recursive-G7-result-v1', 'request': request,
              'terminal_adapter_manifest_sha256': binding['terminal_adapter_manifest_sha256'],
              'actual_source_models_sha256': hashlib.sha256(provider_path.read_bytes()).hexdigest(),
              'actual_source_count': provider['source_count_examined'], 'actual_source_mode_model_count': len(models),
              'complete_original_registry': True, 'catalogue_exhausted': True,
              'symbolic_future_histories': 'Exact real response variables, one whole shared source assignment per model',
              'quantifier_order': 'exists legal action, for all next response, recursively',
              'unknown_size_termination_or_global_NO_claimed': False, 'empirical_admission_claimed': False,
              'Lean_certification_claimed': False, 'software': {'sympy': sp.__version__, 'z3': z3.get_version_string()},
              'generic_adaptive_selector_completeness_claimed': False}
    try:
        engine = WinningFormula(models, supports, row_sites, budget[1], budget[2], pair_cap, node_cap, ms)
    except FormulaLimit as exc:
        report.update(status='UNKNOWN_RECURSIVE_SOURCE_PAIR_RESOURCE_LIMIT', reason=str(exc)); return report
    admission = initial_history_admission(engine, history, ms); report['history_admission'] = admission
    if admission['status'] != 'ACTUAL_HISTORY_ADMITTED_SAME_BACKEND':
        report['status'] = admission['status']; return report
    # In the inherited static affine menu, k base rows bound informative calls.
    remaining = min(budget[0] - len(history), k)
    decision = at_most_budget_decide(engine, history, remaining, old_rows, old_sites, ms)
    report.update(budget_decision=decision, terminal_source_pair_QE=engine.audit,
                  informative_remaining_call_cap=remaining)
    if decision['status'] == 'AT_MOST_BUDGET_FALSE_SAME_BACKEND':
        report['status'] = 'RECURSIVE_BUDGET_NO_COMPLETE_KNOWN_REGISTRY_SAME_BACKEND'
    elif decision['status'] == 'AT_MOST_BUDGET_TRUE_BY_COMPLETED_LOWER_BUDGET_CHECK':
        report['status'] = 'RECURSIVE_BUDGET_TRUE_SELECTOR_EXTRACTION_PENDING'
        if not history:
            selector = search_constant_selector(engine, remaining, selector_cap, ms)
            report['selector_search'] = selector
            if selector['status'] == 'CONSTANT_SELECTOR_EXTRACTED_AND_CERTIFIED_SAME_BACKEND':
                report['status'] = 'RECURSIVE_BUDGET_TRUE_CONCRETE_SELECTOR_CERTIFIED_SAME_BACKEND'
        else:
            report['selector_extraction_limit'] = 'Conditional-history and general adaptive CAD fibres remain pending'
    else:
        report['status'] = decision['status']
    report.update(elapsed_seconds=time.monotonic()-started,
                  trust='Completed symbolic decisions/selector checks use exact same-backend Z3; no generic independent proof certificate')
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__); ap.add_argument('request'); ap.add_argument('--output', required=True)
    args = ap.parse_args(); request = json.loads(Path(args.request).read_text())
    try:
        result = run(request, args.output)
    except (InvalidInput, Unsupported, ValueError, KeyError, TypeError, z3.Z3Exception) as exc:
        result = {'schema': 'actual-source-recursive-G7-result-v1', 'status': 'REJECTED_RECURSIVE_ENCODING',
                  'reason': str(exc), 'empirical_admission_claimed': False}
    directory = Path(args.output); directory.mkdir(parents=True, exist_ok=True)
    (directory / 'RECURSIVE-RESULT.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status', 'actual_source_count', 'actual_source_mode_model_count', 'elapsed_seconds', 'reason']
                      if k in result}, indent=2))


if __name__ == '__main__':
    main()
