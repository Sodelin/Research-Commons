"""Exact bounded G4 evidence; no unknown-size source decision.

Cone and local separator replay use the standard library only. SciPy is an
optional proposal engine for a bounded rational-target separator search.
Full forest computation reuses the inherited rational current-root compiler.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
import json
from math import comb
from pathlib import Path

from .core import InputError, identifier, keys, rational
from .vendor import forest_algebra as F

LOCAL_PROOF_SHA256 = '4b8e43ecb28f15e7c6267811405d8d4041022068b8c354e99067ac364677f9a0'
LIMITATIONS = ('Conditional finite evidence only; no general G4 stopping, '
               'all-rival localization, source admission from stochasticity, '
               'or promotion of forest coordinates to original observations.')


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                             ensure_ascii=True).encode()).hexdigest()


def integer(value, lo, hi, name):
    if isinstance(value, bool) or not isinstance(value, int) or not lo <= value <= hi:
        raise InputError(f'{name}: integer in {lo}..{hi} required')
    return value


def strict(value, name):
    x = rational(value, name)
    if not 0 < x < 1:
        raise InputError(f'{name}: strict rational in (0,1) required')
    return x


def ceil_div(a, b):
    return -((-a) // b)


def log_enclosure(x, digits=100, terms=120):
    """Inclusive integer endpoints at scale 10**digits for rational x>=1."""
    if x < 1:
        raise InputError('log enclosure requires x>=1')
    scale = 10**digits

    def unit(y):
        z = (y-1)/(y+1)
        zl, zu = scale*z.numerator//z.denominator, ceil_div(scale*z.numerator, z.denominator)
        lo, hi = zl, zu
        z2l, z2u = zl*zl//scale, ceil_div(zu*zu, scale)
        sl = su = 0
        for j in range(terms):
            sl += lo//(2*j+1)
            su += ceil_div(hi, 2*j+1)
            lo, hi = lo*z2l//scale, ceil_div(hi*z2u, scale)
        remainder = ceil_div(9*scale, 4*(2*terms+1)*3**(2*terms+1))
        return 2*sl, 2*su+remainder

    k = x.numerator.bit_length()-x.denominator.bit_length()
    while Q(2)**k > x:
        k -= 1
    while Q(2)**(k+1) <= x:
        k += 1
    lo, hi = unit(x/Q(2)**k)
    l2, u2 = unit(Q(2))
    return lo+k*l2, hi+k*u2


def normalized_diagonal(q, g, n):
    return sum((Q(comb(n, j))*g**j*(1-g)**(n-j)*q**(-j*(n-j))
                for j in range(n+1)), Q(0))


def cone_data(request):
    names = ['kind', 'arities', 'target', 'nodes', 'clock_min', 'log_scale_digits', 'atanh_terms']
    keys(request, names, names, 'cone request')
    if request['kind'] != 'finite_log_diagonal_cone_v1':
        raise InputError('Unsupported cone request')
    arities = request['arities']
    if not isinstance(arities, list) or not 1 <= len(arities) <= 15:
        raise InputError('Provide 1..15 arities')
    for n in arities:
        integer(n, 2, 20, 'arity')
    if len(set(arities)) != len(arities):
        raise InputError('Duplicate arity')
    clock = strict(request['clock_min'], 'clock_min')
    if not isinstance(request['nodes'], list) or len(request['nodes']) != len(arities):
        raise InputError('Square cone matrix required')

    def node(data):
        keys(data, ['q', 'g'], ['q', 'g'], 'cell node')
        q, g = strict(data['q'], 'q'), strict(data['g'], 'g')
        if q <= clock:
            raise InputError('Cell survival must exceed the stated COMMON clock')
        return q, g

    target = node(request['target'])
    nodes = [node(x) for x in request['nodes']]
    digits = integer(request['log_scale_digits'], 20, 300, 'log_scale_digits')
    terms = integer(request['atanh_terms'], 20, 400, 'atanh_terms')
    a = [[log_enclosure(normalized_diagonal(q, g, n), digits, terms)
          for q, g in nodes] for n in arities]
    v = [log_enclosure(normalized_diagonal(*target, n), digits, terms) for n in arities]
    return a, v, 10**digits


def check_cone(request, certificate):
    names = ['kind', 'request_sha256', 'proposal_scale_digits', 'inverse_integers', 'weight_integers']
    keys(certificate, names, names, 'cone certificate')
    if certificate['kind'] != 'rational_preconditioned_cone_v1' or certificate['request_sha256'] != digest(request):
        raise InputError('Cone certificate/request binding mismatch')
    a, v, scale = cone_data(request)
    size = len(a)
    bscale = 10**integer(certificate['proposal_scale_digits'], 1, 200, 'proposal_scale_digits')

    def proposal_int(x):
        if not isinstance(x, str) or len(x) > 500:
            raise InputError('Proposal integers must be bounded exact strings')
        try:
            return int(x)
        except ValueError as exc:
            raise InputError('Invalid proposal integer') from exc

    b = certificate['inverse_integers']
    w = certificate['weight_integers']
    if not isinstance(b, list) or len(b) != size or any(not isinstance(row, list) or len(row) != size for row in b):
        raise InputError('Wrong inverse dimensions')
    if not isinstance(w, list) or len(w) != size:
        raise InputError('Wrong weight dimensions')
    b = [[proposal_int(x) for x in row] for row in b]
    w = [proposal_int(x) for x in w]

    def scaled(k, iv):
        lo, hi = iv
        return (k*lo, k*hi) if k >= 0 else (k*hi, k*lo)

    def added(ivs):
        ivs = list(ivs)  # Both endpoint sums must see the same values.
        return sum(iv[0] for iv in ivs), sum(iv[1] for iv in ivs)

    delta = 0
    for i in range(size):
        row = 0
        for j in range(size):
            lo, hi = added(scaled(b[i][k], a[k][j]) for k in range(size))
            diagonal = bscale*scale if i == j else 0
            row += max(abs(diagonal-lo), abs(diagonal-hi))
        delta = max(delta, row)
    delta = Q(delta, bscale*scale)
    if delta >= 1:
        raise InputError('Exact inverse residual does not prove invertibility')
    residual = []
    for i in range(size):
        lo, hi = added(scaled(w[j], a[i][j]) for j in range(size))
        residual.append((bscale*v[i][0]-hi, bscale*v[i][1]-lo))
    rnum = max(max(map(abs, added(scaled(b[i][j], residual[j]) for j in range(size))))
               for i in range(size))
    error = Q(rnum, scale*bscale*bscale)/(1-delta)
    minimum = Q(min(w), bscale)
    if minimum <= error:
        raise InputError('Exact enclosure does not prove every conic weight positive')
    return {'status': 'CERTIFIED_BOUNDED_LOG_CONE', 'request_sha256': digest(request),
            'certificate_sha256': digest(certificate), 'inverse_residual_bound': str(delta),
            'solution_error_bound': str(error), 'minimum_proposed_weight': str(minimum),
            'implication': 'No nonzero linear functional nonnegative at every node can vanish at this target.',
            'limitations': LIMITATIONS+' Conic weights are not source multiplicities or mixtures.'}


# Polynomials in (p,y), represented by (p exponent, y exponent) -> integer.
@lru_cache(None)
def cell_polynomial(n):
    symmetric = [{0: 2}, {0: 1}]
    for k in range(2, n+1):
        row = dict(symmetric[-1])
        for exponent, coefficient in symmetric[-2].items():
            row[exponent+1] = row.get(exponent+1, 0)-coefficient
        symmetric.append({e: c for e, c in row.items() if c})
    out = {}
    for j in range(n//2+1):
        row = {0: 1} if 2*j == n else symmetric[n-2*j]
        for e, c in row.items():
            out[j+e, j*(n-j)] = out.get((j+e, j*(n-j)), 0)+comb(n, j)*c
    return {e: c for e, c in out.items() if c}


def evaluate(poly, p, y):
    return sum((Q(c)*p**i*y**j for (i, j), c in poly.items()), Q(0))


def derivative(poly, axis):
    out = {}
    for powers, c in poly.items():
        if powers[axis]:
            v = list(powers)
            v[axis] -= 1
            out[tuple(v)] = c*powers[axis]
    return out


def absolute_bound(poly, pmax, ymax):
    return sum((abs(Q(c))*pmax**i*ymax**j for (i, j), c in poly.items()), Q(0))


def tangent(n, p, y):
    poly = cell_polynomial(n)
    value = evaluate(poly, p, y)
    return evaluate(derivative(poly, 0), p, y)/value, evaluate(derivative(poly, 1), p, y)/value


def weak_remainder(n):
    """Exact E in R_n=1+p(y-1)D_n+p²(y-1)²E."""
    poly = dict(cell_polynomial(n))
    poly[0, 0] = poly.get((0, 0), 0)-1
    # (y-1)*D_n(y) = n*(y**(n-1)-1).
    poly[1, n-1] = poly.get((1, n-1), 0)-n
    poly[1, 0] = poly.get((1, 0), 0)+n
    groups = {}
    for (i, j), c in poly.items():
        if not c:
            continue
        if i < 2:
            raise ArithmeticError('Weak expansion fails p² divisibility')
        groups.setdefault(i-2, {})[j] = c
    out = {}
    for i, row in groups.items():
        for _ in range(2):
            degree = max(row, default=0)
            quotient = {}
            rem = dict(row)
            for j in range(degree, 0, -1):
                c = rem.get(j, 0)
                if c:
                    quotient[j-1] = c
                    rem[j-1] = rem.get(j-1, 0)+c
            if rem.get(0, 0):
                raise ArithmeticError('Weak expansion fails (y-1)² divisibility')
            row = quotient
        out.update({(i, j): c for j, c in row.items() if c})
    return out


def bernstein(coefficients, left, right, degree):
    """Exact coefficients on [left,right], including degree elevation."""
    power = [Q(0)]*(degree+1)
    for j, coefficient in enumerate(coefficients):
        for k in range(j+1):
            power[k] += coefficient*comb(j, k)*left**(j-k)*(right-left)**k
    return [sum((power[k]*Q(comb(i, k), comb(degree, k)) for k in range(i+1)), Q(0))
            for i in range(degree+1)]


def separator_request(request):
    names = ['kind', 'target_q', 'target_p', 'common_clock', 'provider_sha256']
    keys(request, names, names, 'separator request')
    if request['kind'] != 'rational_local_weak_separator_v1' or request['provider_sha256'] != LOCAL_PROOF_SHA256:
        raise InputError('Unsupported or unpinned local provider')
    q = strict(request['target_q'], 'target_q')
    p = rational(request['target_p'], 'target_p')
    c = strict(request['common_clock'], 'common_clock')
    if not 0 < p < Q(1, 4) or c >= q:
        raise InputError('Biased target requires 0<p<1/4 and 0<c<q<1')
    return p, 1/q, 1/c


def local_constants(p, y, upper, coefficients, d):
    arities = range(2, len(coefficients)+2)
    error = Q(0)
    hessian = [[Q(0), Q(0)], [Q(0), Q(0)]]
    for n, a in zip(arities, coefficients):
        poly = cell_polynomial(n)
        emax = absolute_bound(weak_remainder(n), Q(1, 4), upper)
        dmax = n*sum((upper**j for j in range(n-1)), Q(0))
        error += abs(a)*(emax+(dmax+emax)**2/2)
        first = [derivative(poly, axis) for axis in (0, 1)]
        for i in (0, 1):
            for j in (0, 1):
                hessian[i][j] += abs(a)*(absolute_bound(derivative(first[i], j), Q(1, 4), upper)
                                         +absolute_bound(first[i], Q(1, 4), upper)*absolute_bound(first[j], Q(1, 4), upper))
    epsilon = min(Q(1), d/(2*(error+1)))
    base = min(p/2, (Q(1, 4)-p)/2, (y-1)/2, (upper-y)/2, Q(1))
    pmin, pmax, ymin, ymax = p-base, p+base, y-base, y+base
    w0, wmin = p*(y-1), pmin*(ymin-1)
    r2max, r3max = 1+2*pmax*(ymax-1), 1+3*pmax*(ymax*ymax-1)
    cy = r3max*(upper+1)/wmin+(3*w0*(y+1))*r2max/(3*wmin*w0)
    cp = r2max/(ymin-1)+w0*cy/((ymin-1)*(y-1))
    inverse = max(cp, cy)
    c3 = 2*max(x for row in hessian for x in row)*inverse**2
    sbound = (1+2*epsilon)*((ymax-1)+pmax)
    eta = min(base, d/(8*(c3+1)*(sbound+1)))
    return {'epsilon': str(epsilon), 'eta_p_y_max_norm': str(eta),
            'weak_log_remainder_score_bound': str(error), 'body_inverse_lipschitz_bound': str(inverse),
            'body_score_quadratic_S_bound': str(c3), 'S_per_eta_bound': str(sbound),
            'body_base_rectangle': {'p': [str(pmin), str(pmax)], 'y': [str(ymin), str(ymax)]}}


def check_separator(request, certificate):
    names = ['kind', 'request_sha256', 'coefficients', 'bernstein_degree']
    keys(certificate, names, names, 'local separator certificate')
    if certificate['kind'] != 'tangent_bernstein_separator_v1' or certificate['request_sha256'] != digest(request):
        raise InputError('Local separator certificate/request binding mismatch')
    p, y, upper = separator_request(request)
    values = certificate['coefficients']
    if not isinstance(values, list) or not 3 <= len(values) <= 19:
        raise InputError('Separator arities must be contiguous 2..N, 4<=N<=20')
    a = [rational(x, 'separator coefficient') for x in values]
    degree = integer(certificate['bernstein_degree'], len(a)-1, 100, 'bernstein_degree')
    rows = [tangent(n, p, y) for n in range(2, len(a)+2)]
    if any(sum((v*t[axis] for v, t in zip(a, rows)), Q(0)) for axis in (0, 1)):
        raise InputError('Separator does not annihilate the exact target tangent')
    polynomial = [sum((a[n-2]*n for n in range(j+2, len(a)+2)), Q(0)) for j in range(len(a))]
    bounds = bernstein(polynomial, Q(1), upper, degree)
    d = min(bounds)
    if d <= 0:
        raise InputError('Bernstein certificate does not prove strict positivity on the full interval')
    constants = local_constants(p, y, upper, a, d)
    return {'status': 'CERTIFIED_CONDITIONAL_LOCAL_WEAK_EXCLUSION', 'request_sha256': digest(request),
            'certificate_sha256': digest(certificate), 'arity': len(a)+1,
            'separator_lower_bound': str(d), 'bernstein_coefficients': [str(x) for x in bounds],
            'neighbourhood_constants': constants, 'all_rival_neighbourhood_verified': False,
            'premise': 'One actual equal-arm cell has |p-p0|,|1/q-1/q0|<=eta; every extra cell has p(1/q-1)<=epsilon; same positive COMMON clock and exact normalized diagonals through N.',
            'conclusion': 'Under that premise no extra cells exist and the body has the exact target (q,p). Ordinary pads and chronology are not determined by diagonals.',
            'limitations': LIMITATIONS}


def search_separator(request, max_arity=12, max_degree=40):
    """Bounded candidate search, followed by exact rational acceptance.

    This implements a sufficient Bernstein search for rational targets. It is
    not the provider's complete real-algebraic RCF search and may return UNKNOWN.
    """
    p, y, upper = separator_request(request)
    try:
        import numpy as np
        from scipy.optimize import linprog
    except ImportError:
        return {'status': 'UNKNOWN', 'reason': 'Optional SciPy proposal backend unavailable'}
    attempts = []
    for nmax in range(4, integer(max_arity, 4, 20, 'max_arity')+1):
        rows = [tangent(n, p, y) for n in range(2, nmax+1)]
        determinant = rows[0][0]*rows[1][1]-rows[1][0]*rows[0][1]
        basis = []
        for index in range(2, len(rows)):
            v = [Q(0)]*len(rows)
            v[0] = (-rows[index][0]*rows[1][1]+rows[1][0]*rows[index][1])/determinant
            v[1] = (-rows[0][0]*rows[index][1]+rows[index][0]*rows[0][1])/determinant
            v[index] = Q(1)
            basis.append(v)
        for degree in range(nmax-2, integer(max_degree, nmax-2, 100, 'max_degree')+1, 2):
            columns = []
            for v in basis:
                poly = [sum((v[n-2]*n for n in range(j+2, nmax+1)), Q(0)) for j in range(nmax-1)]
                columns.append(bernstein(poly, Q(1), upper, degree))
            # Row normalization helps discovery; exact replay never trusts it.
            matrix = np.array([[float(col[i]) for col in columns] for i in range(degree+1)])
            norms = np.maximum(np.max(np.abs(matrix), axis=1), 1)
            result = linprog(np.zeros(len(basis)), A_ub=-matrix/norms[:, None],
                             b_ub=-1/norms, bounds=[(None, None)]*len(basis), method='highs')
            attempts.append({'arity': nmax, 'degree': degree, 'proposal_status': int(result.status)})
            if result.success:
                for digits in (8, 12, 16):
                    z = [Q(format(float(x), f'.{digits}g')) for x in result.x]
                    a = [sum((z[j]*basis[j][i] for j in range(len(basis))), Q(0)) for i in range(len(rows))]
                    cert = {'kind': 'tangent_bernstein_separator_v1', 'request_sha256': digest(request),
                            'coefficients': [str(x) for x in a], 'bernstein_degree': degree}
                    try:
                        checked = check_separator(request, cert)
                    except InputError:
                        continue
                    return {'status': 'CERTIFIED_PROPOSAL_FOUND', 'certificate': cert,
                            'checked': checked, 'attempts': attempts}
    return {'status': 'UNKNOWN', 'reason': 'No exact certificate within the declared search budget', 'attempts': attempts}


def word_data(request):
    names = ['kind', 'source_id', 'cap', 'roots', 'parameters', 'chronology']
    keys(request, names, names, 'word request')
    if request['kind'] != 'same_source_private_word_v1':
        raise InputError('Unsupported source alphabet')
    identifier(request['source_id'], 'source_id')
    cap = integer(request['cap'], 1, 4, 'cap')
    roots = request['roots']
    if not isinstance(roots, list) or len(roots) != cap:
        raise InputError('Exactly cap original root IDs required')
    for root in roots:
        keys(root, ['copy_id', 'original_taxon_id'], ['copy_id', 'original_taxon_id'], 'root')
        identifier(root['copy_id'], 'copy_id')
        identifier(root['original_taxon_id'], 'original_taxon_id')
    if len({r['copy_id'] for r in roots}) != cap:
        raise InputError('Duplicate original copy ID')
    bank = request['parameters']
    if not isinstance(bank, dict) or not 1 <= len(bank) <= 100:
        raise InputError('One finite shared parameter bank required')
    bank = {identifier(k, 'parameter ID'): strict(v, k) for k, v in bank.items()}
    sequence = request['chronology']
    if not isinstance(sequence, list) or not 1 <= len(sequence) <= 64:
        raise InputError('Finite chronological word requires 1..64 factors')
    used, occurrences, arms, operations = set(), set(), set(), []
    for factor in sequence:
        if not isinstance(factor, dict):
            raise InputError('Physical factor must be an object')
        allowed = ['kind', 'occurrence_id', 'survival'] if factor.get('kind') == 'ordinary' else ['kind', 'occurrence_id', 'arm_ids', 'left', 'right', 'weight']
        keys(factor, allowed, allowed, 'physical factor')
        occurrence = identifier(factor['occurrence_id'], 'occurrence_id')
        if occurrence in occurrences:
            raise InputError('Duplicate physical occurrence ID')
        occurrences.add(occurrence)
        names = ['survival'] if factor['kind'] == 'ordinary' else ['left', 'right', 'weight']
        values = []
        for name in names:
            ref = factor[name]
            if not isinstance(ref, str) or ref not in bank:
                raise InputError('Every factor must reference the one shared bank')
            used.add(ref)
            values.append(bank[ref])
        if factor['kind'] == 'bigon':
            ids = factor['arm_ids']
            if not isinstance(ids, list) or len(ids) != 2 or len(set(ids)) != 2:
                raise InputError('Two distinct original arm occurrence IDs required')
            for arm in ids:
                identifier(arm, 'arm ID')
                if arm in arms:
                    raise InputError('Reused original arm occurrence ID')
                arms.add(arm)
        elif factor['kind'] != 'ordinary':
            raise InputError('Unknown physical factor')
        operations.append((factor['kind'], tuple(values)))
    if used != set(bank):
        raise InputError('Unused bank entries hide a different physical assignment')
    return cap, operations


def inspect_local_rival(request, separator_request_data, separator_certificate, body_occurrence):
    """Check the local premise on ONE supplied physical word, never all rivals."""
    checked = check_separator(separator_request_data, separator_certificate)
    _, operations = word_data(request)
    p0, y0, _ = separator_request(separator_request_data)
    clock = rational(separator_request_data['common_clock'])
    epsilon = Q(checked['neighbourhood_constants']['epsilon'])
    eta = Q(checked['neighbourhood_constants']['eta_p_y_max_norm'])
    product_clock = Q(1)
    cells = []
    for factor, (kind, values) in zip(request['chronology'], operations):
        if kind == 'ordinary':
            product_clock *= values[0]
        else:
            x, y, g = values
            if x != y:
                return {'status': 'OUTSIDE_LOCAL_PREMISE', 'reason': 'Supplied cell arms differ'}
            product_clock *= x
            cells.append({'id': factor['occurrence_id'], 'p': g*(1-g), 'y': 1/x})
    body = [cell for cell in cells if cell['id'] == body_occurrence]
    if len(body) != 1:
        raise InputError('Designate exactly one actual body cell occurrence')
    extras = [cell for cell in cells if cell['id'] != body_occurrence]
    in_neighbourhood = (abs(body[0]['p']-p0) <= eta and abs(body[0]['y']-y0) <= eta
                        and all(cell['p']*(cell['y']-1) <= epsilon for cell in extras))
    equalities = []
    for n in range(2, checked['arity']+1):
        value = Q(1)
        for cell in cells:
            value *= evaluate(cell_polynomial(n), cell['p'], cell['y'])
        target = evaluate(cell_polynomial(n), p0, y0)
        equalities.append({'arity': n, 'word_normalized_diagonal': str(value),
                           'target_normalized_diagonal': str(target), 'equal': value == target})
    matching = all(row['equal'] for row in equalities)
    premise = product_clock == clock and in_neighbourhood
    return {'status': 'CHECKED_SUPPLIED_LOCAL_RIVAL', 'request_sha256': digest(request),
            'separator_request_sha256': digest(separator_request_data),
            'same_COMMON_clock': product_clock == clock, 'body_and_extras_in_neighbourhood': in_neighbourhood,
            'exact_normalized_diagonals': equalities, 'all_target_diagonals_match': matching,
            'extra_cell_count': len(extras), 'local_neighbourhood_verified': premise,
            'local_theorem_full_premises_verified': premise and matching,
            'exact_diagonal_mismatch_within_neighbourhood': premise and not matching,
            'all_unknown_size_rivals_localized': False,
            'limitations': 'Checks one supplied finite positive source word. No global localization follows.'}


def word_certificate(request):
    cap, operations = word_data(request)
    algebra = F.ForestAlgebra(cap)
    rows, laws = [], {}
    ids = [r['copy_id'] for r in request['roots']]

    def encode(tree):
        return ids[tree] if isinstance(tree, int) else [encode(tree[0]), encode(tree[1])]

    for mode in ('common', 'independent'):
        vector = algebra.unit
        for kind, values in operations:
            operator = algebra.edge(*values) if kind == 'ordinary' else algebra.bigon(*values, mode)
            vector = algebra.mul(vector, operator)
        laws[mode] = vector
        for k in range(1, cap+1):
            law = [(forest, vector[algebra.index[k, forest]]) for forest in F.forests(tuple(range(k)))]
            if any(p < 0 for _, p in law) or sum((p for _, p in law), Q(0)) != 1:
                raise ArithmeticError('Invalid exact full forest law')
            rows.append({'mode': mode, 'entering_roots': k,
                         'coordinates': [{'forest': [encode(t) for t in forest], 'probability': str(p)} for forest, p in law]})
    diagnostics = {}
    if cap >= 3:
        c = laws['common'][algebra.index[2, (0, 1)]]
        b3c = laws['common'][algebra.index[3, (0, 1, 2)]]
        b2i = laws['independent'][algebra.index[2, (0, 1)]]
        b3i = laws['independent'][algebra.index[3, (0, 1, 2)]]
        diagnostics = {'common_clock': str(c), 'COMMON_Jensen_gap': str(b3c-c**3),
                       'r': str(b2i/c), 's': str(b3i/c**3),
                       'paired_nonlinear_gap': str(b3i/c**3-(3*(b2i/c)**2-3*b2i/c+1))}
    if cap == 4:
        vector = laws['independent']
        law = {f: vector[algebra.index[4, f]] for f in F.forests((0, 1, 2, 3))}
        p1 = sum((p for f, p in law.items() if len(f) == 1), Q(0))
        p2 = sum((p for f, p in law.items() if len(f) == 2), Q(0))
        two = sum((p for f, p in law.items() if len(f) == 2 and all(len(F.leaves(t)) == 2 for t in f)), Q(0))
        balanced = sum((p for f, p in law.items() if len(f) == 1 and all(len(F.leaves(t)) == 2 for t in f[0])), Q(0))
        diagnostics.update({'C': str(two-p2/3), 'H': str(balanced-p1/3)})
    return {'kind': 'exact_same_source_forest_certificate_v1', 'request_sha256': digest(request),
            'rows': rows, 'diagnostics': diagnostics,
            'scope': 'Exact supplied private-word kernels in BOTH modes using the same bank and chronology; these are computation coordinates, not additional original observations.'}


def check_word(request, certificate):
    expected = word_certificate(request)
    if certificate != expected:
        raise InputError('Full same-source forest certificate mismatch; every row and coordinate is required')
    return {'status': 'CERTIFIED_SUPPLIED_WORD_KERNEL', 'request_sha256': digest(request),
            'certificate_sha256': digest(certificate), 'rows_checked': len(expected['rows']),
            'coordinates_checked': sum(len(row['coordinates']) for row in expected['rows']),
            'diagnostics': expected['diagnostics'], 'limitations': LIMITATIONS}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['check-cone', 'search-separator', 'check-separator', 'compile-word', 'check-word'])
    parser.add_argument('request', type=Path)
    parser.add_argument('certificate', nargs='?', type=Path)
    parser.add_argument('--max-arity', type=int, default=12)
    parser.add_argument('--max-degree', type=int, default=40)
    args = parser.parse_args()
    try:
        request = json.loads(args.request.read_text())
        if args.command == 'compile-word':
            result = word_certificate(request)
        elif args.command == 'search-separator':
            result = search_separator(request, args.max_arity, args.max_degree)
        else:
            if args.certificate is None:
                raise InputError('Certificate path required')
            certificate = json.loads(args.certificate.read_text())
            function = {'check-cone': check_cone, 'check-separator': check_separator, 'check-word': check_word}[args.command]
            result = function(request, certificate)
    except (InputError, OSError, ValueError, TypeError, KeyError) as exc:
        print(json.dumps({'status': 'REFUSED', 'reason': str(exc)}, indent=2))
        raise SystemExit(2)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
