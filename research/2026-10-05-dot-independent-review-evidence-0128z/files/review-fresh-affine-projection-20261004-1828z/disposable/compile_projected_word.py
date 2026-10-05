"""Fresh source-complete affine supplied-word projection after recovery.

This is a new implementation. Lost FM test summaries are not receipts here.
"""
import ast
import ctypes
import json
from pathlib import Path
import signal
import sys

import sympy as sp
import z3

sys.path.insert(0, str(Path(__file__).resolve().parent / 'providers'))
from compile_leaves import canonical_source_models
from terminal_engine import validate_models
from verify_policy import verify, PolicyLimit
from fourier_motzkin import project_open_cube, ProjectionLimit


def parsed_action(text, names):
    """Keep EVERY written division domain before rational simplification."""
    if type(text) is int:
        text = str(text)
    if not isinstance(text, str):
        raise ValueError('Exact actions require rational text, never floats.')
    domains = []
    def walk(node, depth=0):
        if depth > 64:
            raise ProjectionLimit('Action nesting ceiling64 exceeded; UNKNOWN.')
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return sp.Integer(node.value)
        if isinstance(node, ast.Name) and node.id in names:
            return names[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -walk(node.operand, depth+1)
        if isinstance(node, ast.BinOp):
            left, right = walk(node.left, depth+1), walk(node.right, depth+1)
            if isinstance(node.op, ast.Add):
                return left+right
            if isinstance(node.op, ast.Sub):
                return left-right
            if isinstance(node.op, ast.Mult):
                return left*right
            if isinstance(node.op, ast.Div):
                domains.append(right)
                return left/right
            if (isinstance(node.op, ast.Pow) and isinstance(node.right, ast.Constant)
                    and type(node.right.value) is int and node.right.value >= 0):
                return left ** node.right.value
        raise ValueError('Actions read only earlier observations through exact rational arithmetic.')
    value = walk(ast.parse(text, mode='eval').body)
    return sp.cancel(value), domains


def compile_policy(models, calls, supports, row_sites, budget, milliseconds=3000,
                   max_branches=256, max_pairs=2000, seconds=30, max_nodes=30000):
    receipts = []
    old_handler = old_timer = None
    try:
        if type(seconds) is not int or not 0 < seconds <= 300:
            raise ProjectionLimit('Invalid bounded projection runtime.')
        def timeout(signum, frame):
            raise ProjectionLimit('Projection runtime exceeded; UNKNOWN.')
        old_handler = signal.signal(signal.SIGALRM, timeout)
        old_timer = signal.setitimer(signal.ITIMER_REAL, seconds)
        k, q = validate_models(models)
        original_models = models
        models, source_provenance = canonical_source_models(models)
        if not isinstance(calls, list) or not 0 < len(calls) <= 120:
            raise ProjectionLimit('This finite supplied-word adapter accepts1..120 calls.')
        regions, targets = {}, {}
        for owner, model in enumerate(models):
            names, public_history, history = {}, {}, []
            equations, inequalities = [], []
            for step, call in enumerate(calls):
                if not isinstance(call, dict) or set(call) != {'support', 'weights'}:
                    raise ValueError('Supplied action fields do not match the inherited contract.')
                if not isinstance(call['weights'], list) or len(call['weights']) != k:
                    raise ValueError('Action/source row dimensions mismatch.')
                support = call['support']
                if (not isinstance(support, list) or not support or len(set(support)) != len(support)
                        or any(type(i) is not int or not 0 <= i < k for i in support)):
                    raise ValueError('Malformed configured action support.')
                weights, written_domains = [], []
                for text in call['weights']:
                    weight, domains = parsed_action(text, names)
                    weights.append(weight)
                    written_domains.extend(domains)
                def denominator_domain(expr):
                    numerator, denominator = sp.fraction(sp.cancel(expr))
                    if (numerator.free_symbols | denominator.free_symbols) & set(model['variables']):
                        raise ValueError('Written action domain reads hidden source parameters.')
                    inequalities.append((sp.expand(numerator**2), True))
                    inequalities.append((sp.expand(denominator**2), True))
                for domain in written_domains:
                    denominator_domain(domain)
                for row, weight in enumerate(weights):
                    numerator, denominator = sp.fraction(weight)
                    inequalities.append((sp.expand(denominator**2), True))
                    if row in support:
                        inequalities.append((sp.expand(numerator*denominator), True))
                    else:
                        equations.append(numerator)
                total, total_denominator = sp.fraction(sp.cancel(sum(weights)-1))
                equations.append(total)
                inequalities.append((sp.expand(total_denominator**2), True))
                for coordinate in range(q):
                    observed = sp.Dummy(f'g7History_step{step}_coordinate{coordinate}')
                    history.append(observed)
                    public_name = f'h{step}_{coordinate}'
                    prediction = sum(weights[row]*model['laws'][row][coordinate] for row in range(k))
                    numerator, denominator = sp.fraction(sp.cancel(prediction-observed))
                    if denominator.free_symbols & set(model['variables']):
                        raise ValueError('Source-dependent rational law denominator is unsupported.')
                    equations.append(numerator)
                    inequalities.append((sp.expand(denominator**2), True))
                    public_history[observed] = sp.Symbol(public_name)
                    names[public_name] = observed
            projected = project_open_cube(equations, model['variables'], history, inequalities,
                                          max_branches=max_branches, max_pairs=max_pairs)
            def relation(op, expr):
                if not expr.free_symbols <= set(public_history):
                    raise ValueError('Uneliminated source/auxiliary in a response guard.')
                return {'op': op, 'left': str(expr.xreplace(public_history)), 'right': '0'}
            cells = []
            for cell in projected['cells']:
                guards = [relation({-1:'lt', 0:'eq', 1:'gt'}[sign], factor)
                          for factor, sign in sorted(cell['signs'].items(), key=lambda x: sp.default_sort_key(x[0]))]
                guards += [relation('gt' if strict else 'ge', expr)
                           for expr, strict in cell['inequalities']]
                cells.append({'op': 'and', 'args': guards})
            receipts.append({'source_model': owner, 'source_variables_eliminated': len(model['variables']),
                             'projected_sign_cells': len(cells), 'peak_sign_cells': projected['peak_sign_cells'],
                             'pair_combinations': projected['pair_combinations'],
                             'written_denominator_domains_retained': True,
                             'all_observation_equations_and_source_bounds_jointly_projected': True})
            key = json.dumps(model['target'], sort_keys=True, separators=(',', ':'))
            targets[key] = model['target']
            regions.setdefault(key, []).extend(cells)
        tree = {'kind': 'decision', 'branches': [
            {'guard': {'op': 'or', 'args': regions[key]}, 'next': {'kind': 'leaf', 'target': targets[key]}}
            for key in sorted(regions)]}
        for call in reversed(calls):
            tree = {'kind': 'call', 'support': call['support'], 'weights': call['weights'], 'next': tree}
        checked = verify(original_models, tree, supports, row_sites, budget,
                         milliseconds=milliseconds, max_nodes=max_nodes)
        if checked['status'] != 'FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND':
            return {'status': 'UNKNOWN_OR_REFUTED_PROJECTED_CANDIDATE', 'projection_receipts': receipts,
                    'policy': tree, 'verification': checked, 'mathematical_budget_NO_claimed': False}
        return {'status': 'WHOLE_ACTION_WORD_PROJECTED_AND_VERIFIED_SAME_BACKEND', 'policy': tree,
                'projection_receipts': receipts, 'verification': checked,
                'source_shared_parameters': True, 'written_denominator_domains_retained': True,
                'symbol_identity_provenance': {'sources': source_provenance,
                    'history': 'Independent typed Dummy identity per step/coordinate; public spelling only after source elimination',
                    'actions': 'History-only safe parser with every written division domain retained',
                    'auxiliaries': 'Inherited Z3 FreshReal identities in final verifier'},
                'method': 'Full sign-cell strict affine existential projection plus final whole-policy replay',
                'generic_action_search_or_nonlinear_synthesis_claimed': False,
                'fresh_implementation_after_recovery': True}
    except (ValueError, TypeError, KeyError, AttributeError, SyntaxError, ArithmeticError, RecursionError,
            MemoryError, ctypes.ArgumentError, sp.PolynomialError, z3.Z3Exception, ProjectionLimit, PolicyLimit) as error:
        return {'status': 'UNKNOWN_UNSUPPORTED_OR_RESOURCE_LIMIT', 'reason': str(error),
                'projection_receipts': receipts, 'mathematical_budget_NO_claimed': False}
    finally:
        if old_handler is not None:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old_handler)
            if old_timer and old_timer[0] > 0:
                signal.setitimer(signal.ITIMER_REAL, *old_timer)
