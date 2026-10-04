"""Exact point evaluation of isolated polynomial action sections.

Inputs to this codec are rational observed coordinates and earlier algebraic
sections with rational-coefficient polynomials. General algebraic-coefficient
lifting remains UNKNOWN. The symbolic verifier has the stronger all-real scope.
"""
from fractions import Fraction
import ctypes
import sympy as sp
import z3
from verify_algebraic_policy import expression,PolicyLimit

def select(section,known):
    def exact(text):
        value,defined=expression(text,known);value=z3.simplify(value)
        if not z3.is_true(z3.simplify(defined)) or not z3.is_rational_value(value):
            raise ValueError('This point codec needs defined rational polynomial coefficients/bounds.')
        q=value.as_fraction();return sp.Rational(q.numerator,q.denominator)
    coefficients=[exact(v) for v in section['coefficients']];lower=exact(section['lower']);upper=exact(section['upper'])
    x=sp.Symbol('_action_polynomial_root');poly=sum(v*x**i for i,v in enumerate(coefficients))
    if not poly or not lower<upper:raise ValueError('Invalid section polynomial/interval.')
    roots=sp.real_roots(poly);inside=[]
    for i,root in enumerate(roots):
        if (root-lower).is_positive is True and (upper-root).is_positive is True:
            if not any(sp.simplify(root-v)==0 for j,v in inside):inside.append((i+1,root))
    if len(inside)!=1:raise ValueError('The point section is not uniquely isolated.')
    index,value=inside[0]
    return {'kind':'algebraic','polynomial_ascending':[str(v) for v in coefficients],
            'real_root_index':index},value

def evaluate_section(section,known):
    """Public status boundary; unsupported point codecs remain UNKNOWN."""
    try:
        encoded,value=select(section,known)
        return {'status':'EXACT_ISOLATED_SECTION_POINT','encoding':encoded},value
    except (ValueError,TypeError,KeyError,AttributeError,SyntaxError,NotImplementedError,PolicyLimit,RecursionError,ctypes.ArgumentError,z3.Z3Exception) as error:
        return {'status':'UNKNOWN_UNSUPPORTED_SECTION_POINT','reason':str(error)},None
