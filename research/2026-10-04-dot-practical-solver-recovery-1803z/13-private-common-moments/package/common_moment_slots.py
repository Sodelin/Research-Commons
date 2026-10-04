"""Full COMMON source forest rows from ONE shared sparse-moment family.

Inherited G4 PROOF §3 / ALL-CAP §§1.1,4; not an INDEPENDENT model or a
positive-realization assertion. Original opaque subtrees are still grafted.
"""
from math import comb
from fractions import Fraction
import sympy as sp
from symbolic_core import compile_core  # initializes exact upstream imports
from forest_algebra import edge_polynomials

def shared_moment_rows(max_current_roots,original_slot_id,fresh):
    if type(max_current_roots) is not int or max_current_roots<0:raise ValueError('Actual current-root bound required.')
    moments={0:sp.S.One}
    for j in range(2,max_current_roots+1):
        moments[comb(j,2)]=fresh('common-sparse-moment',[original_slot_id,j],0)
    rows={}
    for k in range(max_current_roots+1):
        rows[k]={forest:sum(sp.Rational(c.numerator,c.denominator)*moments[power] for power,c in coefficients.items())
                 for forest,coefficients in edge_polynomials(k).items()}
    return rows,moments

def actual_word_moments(alg,leading,cells):
    """Exact finite private-COMMON atom expansion of an already supplied word."""
    leading=Fraction(leading)
    if not 0<leading<1:raise ValueError('Every original leading survival is strict-interior.')
    atoms={leading:Fraction(1)}
    for x,y,g,a in cells:
        x,y,g,a=map(Fraction,(x,y,g,a))
        if any(not 0<value<1 for value in (x,y,g,a)):raise ValueError('Every original arm/gamma/connector remains positive finite/interior.')
        nxt={}
        for value,weight in atoms.items():
            for arm,p in ((x,g),(y,1-g)):
                target=value*arm*a;nxt[target]=nxt.get(target,Fraction(0))+weight*p
        atoms=nxt
    moments={comb(j,2):sum(weight*value**comb(j,2) for value,weight in atoms.items()) for j in range(1,alg.m+1)}
    moments[0]=Fraction(1)
    return atoms,moments
