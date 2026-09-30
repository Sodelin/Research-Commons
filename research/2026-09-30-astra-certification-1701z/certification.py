"""Robust CF certification, ASTRA-CERTIFICATION-20260930-1701Z.

Own continuation of the attributed 1612Z biological normal-form compiler.
No automatic full-catalogue computation is performed when this module is imported.
All-class claims require the stated source normal-form theorem. Solver verdicts
are computational evidence, not independently checked proof certificates.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, permutations
from math import isqrt
from pathlib import Path
from typing import Any, Callable, Iterable, Sequence
import ctypes as C
import ctypes.util
import json
import subprocess
import sys
import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'dependencies'))
from cf_normal_form import (Network, Edge, cf, symbolic_model, smt_expression,
                            complete_source_catalogue, support)


def rational(value: Any) -> F:
    """Reject binary floats and booleans at the exact-input boundary."""
    if isinstance(value, (float, bool)):
        raise ValueError('use an exact rational string, integer, or Fraction')
    if isinstance(value, sp.Rational):
        return F(int(value.p), int(value.q))
    return F(value)


@dataclass(frozen=True)
class Algebraic:
    """One real root of a rational polynomial in a rational open interval.

    Coefficients are in descending order. The interval must contain exactly one
    distinct real root and neither endpoint can be a root. The polynomial need
    not be minimal: square-free reduction removes repeated-root ambiguity.
    """
    coefficients: tuple[Any, ...]
    lo: Any
    hi: Any

    def validated(self):
        x = sp.Symbol('isolation_x')
        cs = tuple(rational(c) for c in self.coefficients)
        if len(cs) < 2 or cs[0] == 0:
            raise ValueError('nonconstant polynomial with nonzero leading term required')
        poly = sp.Poly.from_list([sp.Rational(c.numerator, c.denominator) for c in cs], x).sqf_part()
        lo, hi = rational(self.lo), rational(self.hi)
        if not lo < hi:
            raise ValueError('empty isolating interval')
        if poly.eval(lo) == 0 or poly.eval(hi) == 0:
            raise ValueError('isolating interval endpoints must not be roots')
        if poly.count_roots(lo, hi) != 1:
            raise ValueError('interval does not isolate exactly one real root')
        return poly, lo, hi


def polynomial_image_smt(variables: Sequence[sp.Symbol], probabilities: Sequence[Any],
                         observation: Sequence[Any], *, closure: bool = False,
                         boxes: bool = False) -> str:
    """Existential QF_NRA image/closed-image membership; one shared parameter vector.

    Domain is exactly (0,1)^d or [0,1]^d. Extra temporal/edge-floor constraints
    cannot be omitted or handled merely by switching closure=True.
    """
    if len(probabilities) != len(observation) or not probabilities:
        raise ValueError('nonempty matching observation dimension required')
    if len(set(variables)) != len(variables) or not all(isinstance(x, sp.Symbol) for x in variables):
        raise ValueError('distinct symbolic parameters required')
    renamed = {x: sp.Symbol(f'v{i}') for i, x in enumerate(variables)}
    syms = tuple(renamed.values())
    lines = ['(set-logic QF_NRA)']
    cmp = '<=' if closure else '<'
    for x in syms:
        lines.extend([f'(declare-const {x} Real)',
                      f'(assert (and ({cmp} 0 {x}) ({cmp} {x} 1)))'])
    serial = 0

    def encoded_value(value):
        nonlocal serial
        if isinstance(value, Algebraic):
            poly, lo, hi = value.validated()
            z = sp.Symbol(f'a{serial}'); serial += 1
            expr = poly.as_expr().subs(poly.gens[0], z)
            lines.extend([f'(declare-const {z} Real)',
                          f'(assert (= {smt_expression(expr)} 0))',
                          f'(assert (and (< {smt_expression(lo)} {z}) (< {z} {smt_expression(hi)})))'])
            return str(z)
        return smt_expression(rational(value))

    for prob, val in zip(probabilities, observation):
        expr = sp.expand(sp.sympify(prob).xreplace(renamed))
        if expr.free_symbols - set(syms):
            raise ValueError('unbound probability symbol')
        if syms:
            sp.Poly(expr, *syms, domain=sp.QQ)  # reject nonpolynomial/irrational coefficients
        elif not expr.is_Rational:
            raise ValueError('constant probability must be rational')
        encoded_prob = smt_expression(expr)
        if boxes:
            if len(val) != 2:
                raise ValueError('box coordinate must have two rational endpoints')
            lo, hi = map(rational, val)
            if lo > hi:
                raise ValueError('reversed box')
            lines.append(f'(assert (and (<= {smt_expression(lo)} {encoded_prob}) (<= {encoded_prob} {smt_expression(hi)})))')
        else:
            value_text = encoded_value(val)
            lines.append(f'(assert (= {encoded_prob} {value_text}))')
    lines.append('(check-sat-using qfnra-nlsat)')
    return '\n'.join(lines) + '\n'


def graph_image_smt(net: Network, observations: dict, *, mechanism='ind',
                    closure=False, boxes=False) -> str:
    """Compile the actual graph with globally shared edge/inheritance variables."""
    net.source_check(parameters=False)
    if mechanism not in ('ind', 'com'):
        raise ValueError('unknown inheritance mechanism')
    symbolic, variables = symbolic_model(net)
    probs, obs = [], []
    for quartet, values in sorted(observations.items()):
        if tuple(sorted(quartet)) != tuple(quartet) or len(values) != 3:
            raise ValueError('sorted quartets and three coordinates required')
        probs.extend(cf(symbolic, quartet, mechanism)); obs.extend(values)
    return polynomial_image_smt(variables, probs, obs, closure=closure, boxes=boxes)


def solve_in_process(script: str, timeout_ms: int = 10000) -> str:
    """Run trusted generated SMT through libz3. Use bounded_request for isolation."""
    if timeout_ms < 0:
        raise ValueError('negative solver timeout')
    path = ctypes.util.find_library('z3')
    if not path:
        return 'unavailable'
    lib = C.CDLL(path)
    lib.Z3_mk_config.restype = C.c_void_p
    lib.Z3_set_param_value.argtypes = [C.c_void_p, C.c_char_p, C.c_char_p]
    lib.Z3_mk_context.argtypes = [C.c_void_p]; lib.Z3_mk_context.restype = C.c_void_p
    lib.Z3_del_config.argtypes = [C.c_void_p]
    lib.Z3_eval_smtlib2_string.argtypes = [C.c_void_p, C.c_char_p]
    lib.Z3_eval_smtlib2_string.restype = C.c_char_p
    lib.Z3_del_context.argtypes = [C.c_void_p]
    cfg = lib.Z3_mk_config()
    lib.Z3_set_param_value(cfg, b'timeout', str(timeout_ms).encode())
    ctx = lib.Z3_mk_context(cfg); lib.Z3_del_config(cfg)
    try:
        result = lib.Z3_eval_smtlib2_string(ctx, script.encode()).decode().strip()
        return result if result in ('sat', 'unsat', 'unknown') else 'unknown'
    finally:
        lib.Z3_del_context(ctx)


def four_taxon_images(mechanism: str):
    """Six exact all-class n=4 image families, CONDITIONAL on ASTRA-OBS Lemmas 2-3.

    These image parametrizations are not six claimed network graphs. Their
    source attainability is inherited. Closure keeps each interior support label.
    """
    if mechanism not in ('ind', 'com'):
        raise ValueError('unknown mechanism')
    u, v = sp.symbols('u v')
    amin = sp.Rational(1, 6) if mechanism == 'ind' else sp.Rational(1, 3)
    for i in range(3):
        a = amin + (1-amin)*u
        p = [(1-a)/2]*3; p[i] = a
        yield f'T{i}', (u,), tuple(p)
    for i, j in combinations(range(3), 2):
        k = next(k for k in range(3) if k not in (i, j))
        p = [u/3]*3
        p[i] += (1-u)*v; p[j] += (1-u)*(1-v)
        yield f'D{i}{j}', (u, v), tuple(p)


def local_fiber_formula(p, mechanism='ind', closure=False):
    """Independent exact inequality implementation of the six n=4 image sets."""
    if mechanism not in ('ind', 'com'):
        raise ValueError('unknown mechanism')
    p = tuple(map(rational, p))
    if len(p) != 3 or sum(p) != 1 or min(p) < 0:
        return set()
    amin = F(1, 6) if mechanism == 'ind' else F(1, 3)
    out = set()
    for i in range(3):
        j, k = (j for j in range(3) if j != i)
        inside = amin <= p[i] <= 1 if closure else amin < p[i] < 1
        if p[j] == p[k] and inside:
            out.add(f'T{i}')
    for i, j in combinations(range(3), 2):
        k = next(k for k in range(3) if k not in (i, j))
        inside = (p[k] >= 0 and p[i] >= p[k] and p[j] >= p[k]) if closure else (
                  p[k] > 0 and p[i] > p[k] and p[j] > p[k])
        if inside:
            out.add(f'D{i}{j}')
    return out


def local_box_candidates(box, mechanism='ind', solver=solve_in_process):
    """Closed-image outer candidates. An unknown result is retained, never excluded."""
    candidates, witnesses, unknown = [], [], []
    for label, variables, probs in four_taxon_images(mechanism):
        answer = solver(polynomial_image_smt(variables, probs, box, closure=True, boxes=True))
        if answer != 'unsat': candidates.append(label)
        if answer == 'sat': witnesses.append(label)
        elif answer != 'unsat': unknown.append(label)
    return {'outer_candidates': candidates, 'closed_image_witnesses': witnesses,
            'unknown': unknown, 'status': ('MODEL_OR_CONFIDENCE_CONFLICT' if not candidates
              else 'UNIQUE' if len(candidates) == 1 else 'INCONCLUSIVE')}


def radius_bound(dimension: int, m: int, delta=F(1, 20)) -> F:
    """All-prefix Hoeffding radius using integer arithmetic only.

    Risk at prefix m is delta/[m(m+1)]. ceil(log2(A)) >= ln(A) for A>1.
    Dyadic outward square-root rounding has precision that grows with m.
    Clipping a radius above 1 to 1 is valid for coordinates in [0,1].
    """
    delta = rational(delta)
    if isinstance(m, bool) or not isinstance(m, int) or m <= 0:
        raise ValueError('positive integer sample count required')
    if not isinstance(dimension, int) or isinstance(dimension, bool) or dimension < 1 or not 0 < delta < 1:
        raise ValueError('invalid dimension or risk')
    A = F(2*dimension*m*(m+1), 1) / delta
    L = max(0, A.numerator.bit_length() - A.denominator.bit_length())
    if (1 << L)*A.denominator < A.numerator: L += 1
    scale = 1 << max(16, m.bit_length())
    numerator, denominator = L*scale*scale, 2*m
    ceiling = (numerator + denominator - 1)//denominator
    k = isqrt(ceiling)
    if k*k < ceiling: k += 1
    return min(F(1), F(k, scale))


class PrefixBoxes:
    """Nested rational simultaneous boxes for complete quartet count prefixes.

    IID loci and correctly inferred gene quartets are statistical assumptions,
    not something this container can verify from counts. Reuse does not spend
    an additional risk budget for every adaptively selected downstream query.
    """
    def __init__(self, quartets: int, delta=F(1, 20)):
        if not isinstance(quartets, int) or isinstance(quartets, bool) or quartets < 1:
            raise ValueError('positive quartet count required')
        self.k = quartets; self.delta = rational(delta)
        if not 0 < self.delta < 1: raise ValueError('risk must be in (0,1)')
        self.m = 0
        self.counts = [(0, 0, 0)]*quartets
        self.box = [(F(0), F(1))]*(3*quartets)

    def update(self, m: int, counts: Sequence[Sequence[int]]):
        if not isinstance(m, int) or isinstance(m, bool) or m <= self.m:
            raise ValueError('strictly increasing integer prefix required')
        if len(counts) != self.k: raise ValueError('quartet count mismatch')
        cleaned = []
        for old, row in zip(self.counts, counts):
            if len(row) != 3 or any(not isinstance(x, int) or isinstance(x, bool) or x < 0 for x in row):
                raise ValueError('nonnegative integer triple required')
            if sum(row) != m or any(x < y for x, y in zip(row, old)):
                raise ValueError('inconsistent cumulative counts')
            cleaned.append(tuple(row))
        radius = radius_bound(3*self.k, m, self.delta)
        next_box = []
        for old, count in zip(self.box, (x for row in cleaned for x in row)):
            estimate = F(count, m)
            next_box.append((max(old[0], 0, estimate-radius), min(old[1], 1, estimate+radius)))
        self.m, self.counts, self.box = m, cleaned, next_box
        return {'m': m, 'radius': radius, 'box': tuple(self.box),
                'empty': any(lo > hi for lo, hi in self.box)}


def circular_orders(taxa, splits):
    """Exact small-instance order projection. Factorial, not the reviewed fast decoder."""
    taxa = tuple(sorted(taxa))
    if len(taxa) < 3 or len(set(taxa)) != len(taxa):
        raise ValueError('at least three distinct taxa required')
    universe = set(taxa)
    for side, other in splits:
        if not set(side) or not set(other) or set(side) & set(other) or set(side) | set(other) != universe:
            raise ValueError('invalid split')
    result = set()
    for tail in permutations(taxa[1:]):
        order = (taxa[0],) + tail
        if order[1] > order[-1]: continue  # identify reversal
        okay = True
        for side, _ in splits:
            membership = [x in side for x in order]
            if sum(a != b for a, b in zip(membership, membership[1:]+membership[:1])) != 2:
                okay = False; break
        if okay: result.add(order)
    return result


def project_target_set(taxa, candidates):
    """Preserve (split target, order) association; never union quartet-mask bits."""
    if not candidates:
        return {'status': 'MODEL_OR_CONFIDENCE_CONFLICT'}
    candidates = [frozenset(s) for s in candidates]
    common = set.intersection(*(set(s) for s in candidates))
    possible_splits = set.union(*(set(s) for s in candidates))
    by_target = [(s, circular_orders(taxa, s)) for s in candidates]
    possible_orders = set.union(*(o for _, o in by_target))
    safe_orders = set.intersection(*(o for _, o in by_target))
    assert safe_orders == circular_orders(taxa, possible_splits)
    return {'guaranteed_present': common, 'possibly_present': possible_splits,
            'possible_orders': possible_orders, 'universally_valid_orders': safe_orders,
            'target_order_pairs': by_target}


def catalogue_request(request, solver=solve_in_process):
    """Entire generator/compiler/solver controller, intended to run in a subprocess.

    A request is JSON-compatible. Observation rows are [four taxon labels, values].
    The normal-form bound is inherited; a restricted run cannot become all-class.
    """
    taxa = tuple(sorted(request['taxa']))
    if len(taxa) < 4 or len(set(taxa)) != len(taxa): raise ValueError('invalid taxa')
    obs = {tuple(q): values for q, values in request['observations']}
    if len(obs) != len(request['observations']) or set(obs) != set(combinations(taxa, 4)):
        raise ValueError('complete uniquely indexed quartet observations required')
    mechanism = request.get('mechanism', 'ind')
    if mechanism not in ('ind', 'com'): raise ValueError('invalid mechanism')
    closure = request.get('closure', True); boxes = request.get('boxes', False)
    if not isinstance(closure, bool) or not isinstance(boxes, bool): raise ValueError('invalid mode')
    bound = 2*len(taxa)-3
    cap = request.get('max_reticulations', bound)
    limit = request.get('max_graphs')
    if not isinstance(cap, int) or isinstance(cap, bool) or cap < 0: raise ValueError('invalid cap')
    if limit is not None and (not isinstance(limit, int) or isinstance(limit, bool) or limit < 0):
        raise ValueError('invalid graph budget')
    found, unresolved = set(), set()
    visited, exhausted = 0, True
    for net in complete_source_catalogue(len(taxa), cap):
        if limit is not None and visited >= limit:
            exhausted = False; break
        net.leaves = {v: taxa[int(label[1:])] for v, label in net.leaves.items()}
        label = support(net)
        if label not in found:
            answer = solver(graph_image_smt(net, obs, mechanism=mechanism, closure=closure, boxes=boxes))
            if answer == 'sat': found.add(label); unresolved.discard(label)
            elif answer != 'unsat': unresolved.add(label)
        visited += 1
    unresolved -= found
    complete_scope = exhausted and cap >= bound
    outer = found | unresolved if complete_scope else None
    # A nonempty outer singleton is safe under the model/coverage assumption even
    # if a same-labeled model was unknown. It does not prove empirical feasibility.
    status = ('INCONCLUSIVE' if outer is None else 'MODEL_OR_CONFIDENCE_CONFLICT' if not outer
              else 'UNIQUE_OUTER' if len(outer) == 1 else 'INCONCLUSIVE')
    encode = lambda labels: [sorted(list(s)) for s in sorted(labels, key=repr)]
    return {'status': status, 'all_class_outer_candidates': 'ALL_ADMITTED_TARGETS' if outer is None else encode(outer),
            'witnessed_targets': encode(found), 'unknown_visited_targets': encode(unresolved),
            'catalogue_exhausted': exhausted, 'full_scope': complete_scope,
            'graphs_visited': visited, 'bound': bound, 'cap': cap, 'closure': closure,
            'dependency': '1612Z normal-form theorem; independent review pending'}


def bounded_request(request: dict, seconds: float = 5.0):
    """External wall-time cap includes imports, raw graph steps and compilation.

    On expiry the child is killed and reaped by subprocess.run. No invisible work
    continues. No partial candidate list is misrepresented as an outer set.
    """
    if not 0 < seconds < float('inf'): raise ValueError('finite positive runtime cap required')
    try:
        result = subprocess.run([sys.executable, str(Path(__file__).resolve()), '--request-child'],
                                input=json.dumps(request), text=True, capture_output=True,
                                timeout=seconds, check=False)
    except subprocess.TimeoutExpired:
        return {'status': 'INCONCLUSIVE', 'reason': 'external_timeout',
                'all_class_outer_candidates': 'ALL_ADMITTED_TARGETS'}
    if result.returncode:
        return {'status': 'INCONCLUSIVE', 'reason': 'worker_error',
                'all_class_outer_candidates': 'ALL_ADMITTED_TARGETS', 'detail': result.stderr[-1000:]}
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError:
        return {'status': 'INCONCLUSIVE', 'reason': 'invalid_worker_output',
                'all_class_outer_candidates': 'ALL_ADMITTED_TARGETS'}


def _child():
    req = json.load(sys.stdin)
    operation = req.pop('operation', 'catalogue')
    if operation == 'solver': result = {'status': solve_in_process(req['script'], req.get('timeout_ms', 10000))}
    elif operation == 'catalogue': result = catalogue_request(req)
    else: raise ValueError('unknown worker operation')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    if sys.argv[1:] == ['--request-child']:
        _child()
    else:
        print('Import this module or run check_certification.py. No all-class census starts automatically.')
