"""Exact existential projection of a jointly affine open source cube.

Coefficients may be history polynomials. Every coefficient-zero/sign cell is
retained. Resource exhaustion is unsupported/UNKNOWN, never a mathematical NO.
"""
import sympy as sp


class ProjectionLimit(ValueError):
    pass


def factors(expr, history):
    expr = sp.expand(expr)
    if not expr:
        return sp.Integer(0), []
    if not expr.free_symbols:
        if not expr.is_Rational:
            raise ValueError('Projection coefficients must be exact rational polynomials.')
        return expr, []
    if not expr.free_symbols <= set(history):
        raise ValueError('Uneliminated source identity in a sign coefficient.')
    content, fs = sp.factor_list(expr, *history)
    return content, fs


def known_sign(expr, history, signs):
    content, fs = factors(expr, history)
    if not content:
        return 0
    result = 1 if content > 0 else -1
    for factor, power in fs:
        sign = signs.get(factor)
        if sign is None:
            return None
        if not sign:
            return 0
        result *= sign ** power
    return result


def primitive(expr, variables):
    expr = sp.expand(expr)
    if not expr or not expr.free_symbols:
        return expr
    content, part = sp.Poly(expr, *variables, domain=sp.QQ).primitive()
    return sp.expand(part.as_expr() * (1 if content > 0 else -1))


def clean(rows, variables, history, signs):
    result = {}
    for expr, strict in rows:
        expr = primitive(expr, variables)
        sign = known_sign(expr, history, signs) if not expr.free_symbols - set(history) else None
        if sign is not None:
            if sign < 0 or (sign == 0 and strict):
                return None
            continue
        result[expr] = bool(strict or result.get(expr, False))
    return [(expr, result[expr]) for expr in sorted(result, key=sp.default_sort_key)]


def project_open_cube(equations, sources, history, inequalities=(), max_branches=256, max_pairs=2000):
    """Return finite sign cells equivalent to existence of ONE shared source.

    Rows mean expression >=0 (strict=False) or >0 (strict=True). Equations and
    all source bounds are projected together. No separate row fitting occurs.
    """
    if type(max_branches) is not int or max_branches < 1 or type(max_pairs) is not int or max_pairs < 1:
        raise ProjectionLimit('Invalid finite projection resource ceilings.')
    sources, history = list(sources), list(history)
    if len(set(sources + history)) != len(sources) + len(history):
        raise ValueError('Source/history identities must be distinct.')
    variables = sources + history
    rows = list(inequalities)
    for eq in equations:
        rows.extend([(eq, False), (-eq, False)])
    for source in sources:
        rows.extend([(source, True), (1-source, True)])
    for expr, strict in rows:
        if not isinstance(strict, bool):
            raise ValueError('Strictness must be a literal Boolean.')
        expr = sp.sympify(expr)
        if expr.has(sp.Float):
            raise ValueError('Floating projection coefficients are unsupported.')
        if not expr.free_symbols <= set(variables):
            raise ValueError('Unknown source/history symbol.')
        if sources and sp.Poly(expr, *sources).total_degree() > 1:
            raise ValueError('Jointly nonlinear source law is unsupported.')
        sp.Poly(expr, *variables, domain=sp.QQ) if variables else sp.Rational(expr)
    initial = clean(rows, variables, history, {})
    states = [] if initial is None else [(initial, {})]
    peak = len(states)
    pairs = 0
    for source in reversed(sources):
        next_states = []
        for current, signs in states:
            coefficients = [sp.expand(expr).coeff(source) for expr, _ in current]
            missing = []
            for coefficient in coefficients:
                _, fs = factors(coefficient, history)
                for factor, _ in fs:
                    if factor not in signs and factor not in missing:
                        missing.append(factor)
            pending = [(current, signs)]
            for factor in missing:
                expanded = []
                for old_rows, old_signs in pending:
                    for sign in (-1, 0, 1):
                        new_signs = {**old_signs, factor: sign}
                        new_rows = clean(old_rows, variables, history, new_signs)
                        if new_rows is not None:
                            expanded.append((new_rows, new_signs))
                pending = expanded
                if len(pending) + len(next_states) > max_branches:
                    raise ProjectionLimit('History sign-cell ceiling exceeded; UNKNOWN.')
                peak = max(peak, len(pending) + len(next_states))
            for old_rows, cell in pending:
                positive, negative, zero = [], [], []
                for expr, strict in old_rows:
                    coefficient = sp.expand(expr).coeff(source)
                    remainder = sp.expand(expr-coefficient*source)
                    sign = known_sign(coefficient, history, cell)
                    if sign is None:
                        raise ValueError('Incomplete sign partition.')
                    if sign > 0:
                        positive.append((coefficient, remainder, strict))
                    elif sign < 0:
                        negative.append((coefficient, remainder, strict))
                    else:
                        zero.append((remainder, strict))
                pairs += len(positive) * len(negative)
                if len(positive) * len(negative) + len(zero) > max_pairs:
                    raise ProjectionLimit('Fourier–Motzkin pair ceiling exceeded; UNKNOWN.')
                projected = zero + [(sp.expand((-c)*b+a*d), bool(bs or ds))
                                    for a, b, bs in positive for c, d, ds in negative]
                reduced = clean(projected, variables, history, cell)
                if reduced is not None:
                    next_states.append((reduced, cell))
                    if len(next_states) > max_branches:
                        raise ProjectionLimit('History sign-cell ceiling exceeded; UNKNOWN.')
        states = next_states
    cells = []
    seen = set()
    for rows, signs in states:
        if any(expr.free_symbols - set(history) for expr, _ in rows):
            raise ValueError('Source variable survived existential projection.')
        cell = {'signs': signs, 'inequalities': rows}
        key = (tuple(sorted(signs.items(), key=lambda v: sp.default_sort_key(v[0]))), tuple(rows))
        if key not in seen:
            seen.add(key)
            cells.append(cell)
    return {'cells': cells, 'source_variables_eliminated': len(sources),
            'peak_sign_cells': peak, 'pair_combinations': pairs,
            'method': 'joint strict Fourier–Motzkin projection with complete coefficient sign cells'}
