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


def project_branch_word(models, calls, supports, row_sites, budget, milliseconds=3000,
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
        if not isinstance(models, (list, tuple)) or not models:
            raise ValueError('Source models require a nonempty finite carrier.')
        for model in models:
            if not isinstance(model, dict):
                raise ValueError('Malformed source model carrier.')
            laws = model.get('laws')
            if (not isinstance(laws, (list, tuple)) or not laws
                    or any(not isinstance(row, (list, tuple)) or not row for row in laws)):
                raise ValueError('Source laws require nonempty row and response carriers.')
        k, q = validate_models(models)
        original_models = models
        models, source_provenance = canonical_source_models(models)
        if not isinstance(calls, list) or not 0 < len(calls) <= 120:
            raise ProjectionLimit('This finite supplied-word adapter accepts1..120 calls.')
        if (not isinstance(supports, list) or not supports
                or any(not isinstance(s, (list, tuple)) or not s
                       or any(type(i) is not int or not 0 <= i < k for i in s)
                       or len(set(s)) != len(s) for s in supports)):
            raise ValueError('Unsupported configured action support menu.')
        if (not isinstance(row_sites, (list, tuple)) or len(row_sites) != k
                or any(not isinstance(s, (list, tuple, set))
                       or any(not isinstance(site, str) for site in s) for s in row_sites)):
            raise ValueError('Original row-site carrier mismatch.')
        if (not isinstance(budget, list) or len(budget) != 3
                or any(type(n) is not int or n < 0 for n in budget)):
            raise ValueError('Invalid declared PATH [calls,configurations,sites] budget.')
        allowed = {tuple(sorted(s)) for s in supports}
        used_rows, used_sites = set(), set()
        for call in calls:
            if not isinstance(call, dict) or set(call) != {'support', 'weights'}:
                raise ValueError('Supplied action fields do not match the inherited contract.')
            support = call['support']
            if (not isinstance(support, list) or not support
                    or any(type(i) is not int or not 0 <= i < k for i in support)
                    or len(set(support)) != len(support)):
                raise ValueError('Malformed configured action support.')
            if tuple(sorted(support)) not in allowed:
                raise ValueError('Supplied word uses a support outside the configured menu.')
            used_rows.update(support)
            for row in support:
                used_sites.update(row_sites[row])
        declared_cost = [len(calls), len(used_rows), len(used_sites)]
        if any(cost > limit for cost, limit in zip(declared_cost, budget)):
            raise ValueError('Supplied word exceeds the declared PATH union budget.')
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
        return {'status': 'COMPLETE_AFFINE_LEGAL_WORD_TARGET_REGIONS_PROJECTED',
                'policy_candidate': tree, 'projection_receipts': receipts,
                'source_shared_parameters': True, 'written_denominator_domains_retained': True,
                'source_identity_provenance': source_provenance,
                'whole_word_globally_verified': False,
                'configured_menu_and_declared_PATH_preflight': True,
                'declared_word_PATH_cost': declared_cost,
                'external_physical_footprint_admission_claimed': False,
                'meaning': 'Exact target image for every legal whole-word history; conditional branch correctness requires final source-policy verification',
                'generic_recursive_synthesis_claimed': False}
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, SyntaxError, ArithmeticError, RecursionError,
            MemoryError, ctypes.ArgumentError, sp.PolynomialError, z3.Z3Exception, ProjectionLimit, PolicyLimit) as error:
        return {'status': 'UNKNOWN_UNSUPPORTED_OR_RESOURCE_LIMIT', 'reason': str(error),
                'projection_receipts': receipts, 'mathematical_budget_NO_claimed': False}
    finally:
        if old_handler is not None:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old_handler)
            if old_timer and old_timer[0] > 0:
                signal.setitimer(signal.ITIMER_REAL, *old_timer)
