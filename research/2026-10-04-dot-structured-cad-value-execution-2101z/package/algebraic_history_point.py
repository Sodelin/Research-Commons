"""Exact isolated sections at closed real-algebraic observed histories.

The symbolic all-history policy proof is separate. This executor performs
bounded exact QF_NRA checks and emits replayable rational-polynomial roots.
It never approximates a coefficient, silently chooses one of multiple roots,
or treats an unsupported point as a mathematical NO.
"""
import ctypes
import re
from fractions import Fraction
from math import lcm
import z3
from verify_algebraic_policy import expression, PolicyLimit

class PointLimit(RuntimeError):
    pass

def encode_exact(value):
    value = z3.simplify(value)
    if z3.is_rational_value(value):
        return {'kind': 'rational', 'value': str(value.as_fraction())}
    if isinstance(value, z3.AlgebraicNumRef):
        return {'kind': 'algebraic',
                'polynomial_ascending': [str(v.as_fraction()) for v in value.poly()],
                'real_root_index': value.index()}
    raise ValueError('Expected a closed exact real algebraic value.')

def decode_exact(record):
    if not isinstance(record, dict):
        raise ValueError('Exact values require a structured encoding.')
    if set(record) == {'kind', 'value'} and record['kind'] == 'rational':
        if not isinstance(record['value'], str):
            raise ValueError('Rational values require exact string coefficients.')
        return z3.RealVal(str(Fraction(record['value'])))
    if set(record) != {'kind', 'polynomial_ascending', 'real_root_index'} or record['kind'] != 'algebraic':
        raise ValueError('Unknown exact real value encoding.')
    coeff = record['polynomial_ascending']; index = record['real_root_index']
    if not isinstance(coeff, list) or len(coeff) < 2 or not all(isinstance(c, str) for c in coeff):
        raise ValueError('A real algebraic encoding needs exact rational coefficients.')
    if type(index) is not int or index < 1:
        raise ValueError('Invalid real-root index.')
    coeff = [Fraction(c) for c in coeff]
    if not coeff[-1]:
        raise ValueError('The defining polynomial has zero leading coefficient.')
    scale = lcm(*(c.denominator for c in coeff))
    terms = ['(* ' + z3.IntVal(int(c * scale)).sexpr() + ' (^ x ' + str(i) + '))'
             for i, c in enumerate(coeff) if c]
    poly = '(+ ' + ' '.join(terms) + ')' if len(terms) > 1 else terms[0]
    # Every token in this reconstruction is parsed integer arithmetic. No
    # supplied SMT text or external/source parameter is evaluated.
    parsed = z3.parse_smt2_string('(declare-fun exactObserved () Real) '
             '(assert (= exactObserved (root-obj ' + poly + ' ' + str(index) + ')))')
    if len(parsed) != 1 or not z3.is_eq(parsed[0]):
        raise ValueError('Malformed real algebraic constant.')
    value = z3.simplify(parsed[0].arg(1))
    if not isinstance(value, z3.AlgebraicNumRef) and not z3.is_rational_value(value):
        raise ValueError('Root encoding did not define a closed real algebraic value.')
    return value

def select_exact(section, known, milliseconds=3000):
    if type(milliseconds) is not int or not 0 < milliseconds <= 60000:
        raise ValueError('Invalid point resource ceiling.')
    if not isinstance(section, dict) or set(section) != {'name', 'coefficients', 'lower', 'upper'}:
        raise ValueError('Malformed polynomial section.')
    if not isinstance(section['name'], str) or not section['name'].startswith('action_root_') or not section['name'].isidentifier():
        raise ValueError('Invalid section coordinate name.')
    if not isinstance(known, dict) or section['name'] in known:
        raise ValueError('Section names must be fresh in the observed scope.')
    # The caller may supply only already observed coordinates and earlier own
    # section values. Hidden source/future symbols cannot survive this check.
    scope = {}
    for name, value in known.items():
        if not isinstance(name, str) or not name.isidentifier() or not re.fullmatch(r'(h[0-9]+_[0-9]+|action_root_[A-Za-z0-9_]+)', name):
            raise ValueError('The point scope contains a non-observation/non-section name.')
        if isinstance(value, dict):
            value = decode_exact(value)
        if not isinstance(value, z3.ArithRef):
            raise ValueError('Observed values must have exact real encodings.')
        scope[name] = decode_exact(encode_exact(value))
    coeff = section['coefficients']
    if not isinstance(coeff, list) or len(coeff) < 2:
        raise ValueError('A section needs a nonconstant polynomial encoding.')
    values = [expression(v, scope) for v in coeff]
    lo, lov = expression(section['lower'], scope)
    hi, hiv = expression(section['upper'], scope)
    # Check written denominator domains before any cancellation, including
    # factors written under exponent zero. The borrowed parser records them.
    defined = z3.simplify(z3.And(lov, hiv, *[d for v, d in values]))
    if not z3.is_true(defined):
        raise ValueError('A coefficient or bound has an undefined written domain.')
    coefficients = [z3.simplify(v) for v, d in values]
    for value in coefficients + [lo, hi]:
        encode_exact(value)
    root = z3.FreshReal('isolatedObservedPoint')
    polynomial = sum(v * (z3.RealVal(1) if i == 0 else root ** i)
                     for i, v in enumerate(coefficients))
    solver = z3.SolverFor('QF_NRA'); solver.set(timeout=milliseconds)
    solver.add(lo < root, root < hi, polynomial == 0)
    receipts = []
    result = solver.check()
    receipts.append({'kind': 'point_exists', 'status': str(result), 'query_smt2': solver.to_smt2()})
    if result == z3.unknown:
        raise PointLimit('Exact point existence returned UNKNOWN: ' + solver.reason_unknown())
    if result != z3.sat:
        raise ValueError('No section root lies in the supplied open interval.')
    value = z3.simplify(solver.model().eval(root, model_completion=True))
    encoding = encode_exact(value)
    replay = decode_exact(encoding)
    if not z3.is_true(z3.simplify(replay == value)):
        raise ValueError('Exact root codec failed to round trip.')
    solver.add(root != replay)
    result = solver.check()
    receipts.append({'kind': 'point_unique', 'status': str(result), 'query_smt2': solver.to_smt2()})
    if result == z3.unknown:
        raise PointLimit('Exact point uniqueness returned UNKNOWN: ' + solver.reason_unknown())
    if result != z3.unsat:
        raise ValueError('The supplied interval has multiple distinct section roots.')
    return {'status': 'EXACT_ALGEBRAIC_HISTORY_SECTION_POINT_SAME_BACKEND',
            'encoding': encoding, 'receipts': receipts,
            'trust': 'exact closed algebraic arithmetic and Z3 QF_NRA; symbolic all-history verification is separate'}, value

def evaluate_section(section, known, milliseconds=3000):
    """Public fail-closed boundary. No unsupported input is a NO certificate."""
    try:
        return select_exact(section, known, milliseconds)
    except (PointLimit, PolicyLimit, RecursionError, MemoryError, ctypes.ArgumentError) as error:
        return {'status': 'UNKNOWN_SECTION_POINT_RESOURCE_LIMIT', 'reason': str(error)}, None
    except (ValueError, TypeError, KeyError, AttributeError, IndexError, SyntaxError, ZeroDivisionError, OverflowError,
            NotImplementedError, z3.Z3Exception) as error:
        return {'status': 'UNKNOWN_UNSUPPORTED_SECTION_POINT', 'reason': str(error)}, None
