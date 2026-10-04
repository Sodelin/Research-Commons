"""Inherited G7 recursion with symbolic joint histories and terminal reduction.

The exact quantifier order is EXISTS legal action, FOR ALL next response.
Only the one-remaining-call branch replaces the response by pairwise collision.
These are mathematical source predicates; completed backend decisions are
explicitly trusted Z3/QE until an independent certificate is delivered.
"""
import sys
from pathlib import Path
import time
import z3

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'terminalkit'))
from terminal_engine import (validate_models, polynomial_to_z3,
                             different_target_pairs, different_target_pair_count)


class FormulaLimit(RuntimeError):
    pass


def quantified(variables, formula, universal=False):
    if not variables:
        return formula
    return z3.ForAll(variables, formula) if universal else z3.Exists(variables, formula)


class WinningFormula:
    def __init__(self, models, supports, row_sites, row_cap, site_cap, max_pairs=500, max_nodes=10000,
                 terminal_pair_qe_ms=3000):
        self.k, self.q = validate_models(models)
        if len(row_sites) != self.k or not supports:
            raise ValueError('Actual row-site and support carrier mismatch')
        if any(not s or len(s) != len(set(s)) or any(type(i) is not int or not 0 <= i < self.k for i in s)
               for s in supports):
            raise ValueError('Illegal action support')
        if type(row_cap) is not int or type(site_cap) is not int or min(row_cap, site_cap) < 0:
            raise ValueError('Invalid discrete PATH caps')
        if different_target_pair_count(models) > max_pairs:
            raise FormulaLimit('Complete original source pair carrier exceeds its resource budget')
        self.models = models; self.supports = supports; self.row_sites = [set(s) for s in row_sites]
        self.row_cap = row_cap; self.site_cap = site_cap; self.max_nodes = max_nodes
        self.pairs = different_target_pairs(models); self.nodes = 0; self.audit = []
        self.terminal_pair_qe_ms = terminal_pair_qe_ms

    def consistency(self, model, symbols, history):
        # Build each source's entire history with ONE original parameter map.
        constraints = [z3.And(v > 0, v < 1) for v in symbols.values()]
        laws = [[polynomial_to_z3(p, symbols) for p in row] for row in model['laws']]
        for weights, response in history:
            if len(weights) != self.k or len(response) != self.q:
                raise ValueError('Symbolic history cannot truncate row/response coordinates')
            constraints += [sum(weights[i] * laws[i][j] for i in range(self.k)) == response[j]
                            for j in range(self.q)]
        return laws, constraints

    def pair_collision(self, a, b, history, proposed=None, free_conditions=()):
        left, right = self.models[a], self.models[b]
        amap = {s: z3.FreshReal('originalSourceA') for s in left['variables']}
        bmap = {s: z3.FreshReal('originalSourceB') for s in right['variables']}
        alaws, ac = self.consistency(left, amap, history)
        blaws, bc = self.consistency(right, bmap, history)
        equations = []
        if proposed is not None:
            equations = [sum(proposed[i] * alaws[i][j] for i in range(self.k))
                         == sum(proposed[i] * blaws[i][j] for i in range(self.k)) for j in range(self.q)]
        return quantified(list(amap.values()) + list(bmap.values()), z3.And(*(ac + bc + equations + list(free_conditions))))

    def homogeneous(self, history):
        return z3.And(*[z3.Not(self.pair_collision(i, j, history)) for i, j in self.pairs])

    def action(self, support):
        # Singleton simplex normalization preserves the full real action menu.
        weights = [z3.RealVal(0)] * self.k
        if len(support) == 1:
            weights[support[0]] = z3.RealVal(1)
            return [], weights, z3.BoolVal(True)
        variables = [z3.FreshReal('originalActionWeight') for _ in support[:-1]]
        for i, w in zip(support[:-1], variables):
            weights[i] = w
        weights[support[-1]] = z3.RealVal(1) - sum(variables)
        legal = z3.And(*[weights[i] > 0 for i in support])
        return variables, weights, legal

    def legal_extensions(self, used_rows, used_sites):
        for support in self.supports:
            rows = set(used_rows) | set(support)
            sites = set(used_sites) | set().union(*(self.row_sites[i] for i in support))
            if len(rows) <= self.row_cap and len(sites) <= self.site_cap:
                yield support, rows, sites

    def win(self, history, depth, used_rows=(), used_sites=()):
        self.nodes += 1
        if self.nodes > self.max_nodes:
            raise FormulaLimit('Recursive formula node resource budget exceeded')
        if type(depth) is not int or depth < 0:
            raise ValueError('Invalid remaining call count')
        hom = self.homogeneous(history)
        if depth == 0:
            return hom
        extensions = []
        for support, rows, sites in self.legal_extensions(used_rows, used_sites):
            variables, weights, legal = self.action(support)
            if depth == 1:
                # Equivalent to FOR ALL response: homogeneous(history + response).
                collisions = []
                for i, j in self.pairs:
                    # If the new call already excludes a pair without ANY old
                    # observations, adding history cannot create that collision.
                    # Preserve the complete source-QE receipt for this shortcut.
                    if history:
                        unconditional = self.pair_collision(i, j, [], weights, [legal])
                        base_goal = z3.Goal(); base_goal.add(unconditional)
                        try:
                            base = z3.TryFor(z3.Tactic('qe'), self.terminal_pair_qe_ms)(base_goal).as_expr()
                        except z3.Z3Exception:
                            base = unconditional
                        if z3.is_false(z3.simplify(base)):
                            self.audit.append({'kind': 'history_cannot_create_excluded_collision',
                                               'source_pair': [i, j], 'history_length': len(history),
                                               'complete': True, 'raw_collision_smt2': unconditional.sexpr(),
                                               'reduced_collision_smt2': 'false'})
                            collisions.append(z3.BoolVal(False))
                            continue
                    raw = self.pair_collision(i, j, history, weights, [legal])
                    # Reuse the accepted terminal optimization: eliminate ONLY
                    # source parameters per pair while action/history stay free.
                    # Putting legal outside/inside this collision is equivalent
                    # on the branch's outer legal action domain.
                    goal = z3.Goal(); goal.add(raw)
                    try:
                        reduced = z3.TryFor(z3.Tactic('qe'), self.terminal_pair_qe_ms)(goal).as_expr()
                    except z3.Z3Exception:
                        reduced = raw
                    from terminal_engine import has_quantifier
                    self.audit.append({'kind': 'terminal_pair_source_QE', 'source_pair': [i, j],
                                       'history_length': len(history), 'complete': not has_quantifier(reduced),
                                       'raw_collision_smt2': raw.sexpr(),
                                       'reduced_collision_smt2': reduced.sexpr()})
                    # A partial result is retained exactly, never called FALSE.
                    collisions.append(reduced)
                branch = z3.And(legal, *[z3.Not(x) for x in collisions])
            else:
                response = [z3.FreshReal('actualNextResponse') for _ in range(self.q)]
                continuation = self.win(history + [(weights, response)], depth - 1, rows, sites)
                branch = z3.And(legal, z3.ForAll(response, continuation))
            extensions.append(quantified(variables, branch))
        return z3.Or(hom, *extensions)

    def fixed_policy_counterexample(self, programme_weights):
        """Full SAME-source collision across all calls of a fixed policy.

        This verifies that concrete selector only. It does not certify generic
        history-dependent selector extraction or change the recursive formula.
        """
        for weights in programme_weights:
            if len(weights) != self.k:
                raise ValueError('Fixed selector has wrong row carrier')
        collisions = []
        for i, j in self.pairs:
            a, b = self.models[i], self.models[j]
            amap = {s: z3.FreshReal('fixedSourceA') for s in a['variables']}
            bmap = {s: z3.FreshReal('fixedSourceB') for s in b['variables']}
            alaws, ac = self.consistency(a, amap, [])
            blaws, bc = self.consistency(b, bmap, [])
            constraints = ac + bc
            for weights in programme_weights:
                constraints += [sum(weights[r] * alaws[r][c] for r in range(self.k))
                                == sum(weights[r] * blaws[r][c] for r in range(self.k)) for c in range(self.q)]
            collisions.append(quantified(list(amap.values()) + list(bmap.values()), z3.And(*constraints)))
        return z3.Or(*collisions)


def backend_decide(formula, milliseconds=5000, return_ast=False):
    goal = z3.Goal(); goal.add(formula); started = time.monotonic()
    try:
        reduced = z3.TryFor(z3.Tactic('qe'), milliseconds)(goal).as_expr()
    except z3.Z3Exception as exc:
        return {'status': 'UNKNOWN_RECURSIVE_QE_RESOURCE_LIMIT', 'reason': str(exc)}
    from terminal_engine import has_quantifier
    simplified = z3.simplify(reduced)
    receipt = {'input_formula_smt2': formula.sexpr(), 'reduced_formula_smt2': simplified.sexpr(),
               'elapsed_seconds': time.monotonic() - started, 'z3': z3.get_version_string(),
               'trust': 'completed exact Z3 symbolic QE, not an independently proof-checked certificate'}
    if has_quantifier(simplified):
        receipt['status'] = 'UNKNOWN_PARTIAL_RECURSIVE_QE'
    elif z3.is_true(simplified):
        receipt['status'] = 'CLOSED_RECURSIVE_BUDGET_TRUE_SAME_BACKEND'
    elif z3.is_false(simplified):
        receipt['status'] = 'CLOSED_RECURSIVE_BUDGET_FALSE_SAME_BACKEND'
    else:
        receipt['status'] = 'FREE_SYMBOLIC_HISTORY_RELATION_SAME_BACKEND'
    if return_ast:
        receipt['_formula_ast'] = simplified
    return receipt


def at_most_budget_decide(engine, history, max_programs, used_rows=(), used_sites=(), milliseconds=5000):
    """Reuse a completed smaller-budget win before difficult longer recursion.

    Stopping is allowed at every homogeneous history. Therefore a strategy
    using at most d calls is legal for any larger call cap with the SAME row
    and site caps. An UNKNOWN lower-budget check is never treated as FALSE.
    """
    receipts = []
    for depth in range(max_programs + 1):
        try:
            formula = engine.win(history, depth, used_rows, used_sites)
        except FormulaLimit as exc:
            return {'status': 'UNKNOWN_RECURSIVE_FORMULA_RESOURCE_LIMIT', 'reason': str(exc), 'receipts': receipts}
        result = backend_decide(formula, milliseconds)
        receipts.append({'remaining_programmes': depth, 'check': result})
        if result['status'] == 'CLOSED_RECURSIVE_BUDGET_TRUE_SAME_BACKEND':
            return {'status': 'AT_MOST_BUDGET_TRUE_BY_COMPLETED_LOWER_BUDGET_CHECK',
                    'requested_remaining_programmes': max_programs, 'winning_remaining_programmes': depth,
                    'same_row_and_original_site_caps': [engine.row_cap, engine.site_cap], 'receipts': receipts,
                    'selector_extracted': False}
    final = receipts[-1]['check']
    return {'status': 'AT_MOST_BUDGET_FALSE_SAME_BACKEND'
            if final['status'] == 'CLOSED_RECURSIVE_BUDGET_FALSE_SAME_BACKEND'
            else 'UNKNOWN_RECURSIVE_BUDGET', 'requested_remaining_programmes': max_programs,
            'receipts': receipts, 'selector_extracted': False}
