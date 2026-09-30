"""Robust anytime passive CF boxes for the biological owner's controller.

This builds a sound outer confidence box; it does NOT enumerate graphs, solve
the biological images, or infer a noise bound. Output follows the actual peer
model_image_smt/classify_global_cf boxes=True API at Git blob 4847e9f...
"""
from itertools import combinations
from numbers import Integral
from fractions import Fraction as F
from robust_support import rational,radius_squared
from law_feasibility import upper_root


def ideal_cf_boxes(taxa,counts,delta,*,tv_error=0,anytime=True):
    labels=tuple(sorted(taxa))
    if len(labels)<4 or len(set(labels))!=len(labels):
        raise ValueError('at least four distinct comparable taxa required')
    quartets=tuple(combinations(labels,4))
    if set(counts)!=set(quartets):
        raise ValueError('complete sorted quartet count vector required')
    epsilon=rational(tv_error,'tv_error')
    if not 0<=epsilon<=1:raise ValueError('tv_error must be in [0,1]')
    radius_squared(1,1,len(quartets),delta,anytime=anytime)
    totals=[]
    for q in quartets:
        row=tuple(counts[q])
        if len(row)!=3 or any(isinstance(x,bool) or not isinstance(x,Integral) or x<0 for x in row):
            raise ValueError('three nonnegative integer counts per quartet')
        totals.append(int(sum(row)))
    if len(set(totals))!=1:raise ValueError('all quartets must use the same unique-locus prefix')
    n=totals[0]
    if n==0:return {q:((F(0),F(1)),)*3 for q in quartets}
    rho=upper_root(radius_squared(n,1,len(quartets),delta,anytime=anytime),n)+epsilon
    return {q:tuple((max(F(0),F(int(x),n)-rho),min(F(1),F(int(x),n)+rho)) for x in counts[q]) for q in quartets}


def safe_controller_answer(result):
    """Interpret the peer controller without treating found targets as outer.

    Trusts the peer's full-class completeness/solver semantics. Does not certify
    their truth. A production solver must justify unsat and handle unknown.
    """
    status=result.get('full_class_status')
    outer=result.get('all_class_outer_candidates')
    if status=='unique' and isinstance(outer,(set,frozenset)) and len(outer)==1:
        return {'status':'CERTIFIED','target':next(iter(outer))}
    if status=='infeasible' and isinstance(outer,(set,frozenset)) and not outer:
        return {'status':'MODEL_INCOMPATIBLE','target':None}
    return {'status':'INCONCLUSIVE','target':None}
