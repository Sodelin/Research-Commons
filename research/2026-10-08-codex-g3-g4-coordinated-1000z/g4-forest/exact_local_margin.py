"""Exact dual certificate for a local linear common-zero correction radius.

High precision chooses a covector; only rational arithmetic authenticates the
certificate. No result is asserted about nonlinear or one-sided large moves.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import sys
import time
import types

NEWTON_SHA="a98763e657410860b6240538ec41a5e3659362707d1e0ebe85a49a82d150f3cb"

def load_newton():
    p=Path(__file__).with_name("bounded_common_zero.py")
    b=p.read_bytes()
    if sha256(b).hexdigest()!=NEWTON_SHA:
        raise ValueError("Frozen Newton provider identity mismatch")
    m=types.ModuleType("authenticated_newton_provider")
    m.__file__=str(p)
    exec(compile(b,str(p),"exec"),m.__dict__)
    return m

def vm(v,a):
    out=[F(0)]*len(v)
    for k,c in enumerate(v):
        if c:
            for j,d in enumerate(a[k]):
                if d:
                    out[j]+=c*d
    return out
def mv(a,v):
    return [sum((c*d for c,d in zip(row,v) if c and d),F(0)) for row in a]
def dot(a,b):
    return sum((x*y for x,y in zip(a,b) if x and y),F(0))
def ordinary(E,z):
    return [[sum((c*z**e for e,c in p.items()),F(0)) for p in row] for row in E]

def branch_scalar(p,q,s,h2):
    low=min(p,q)
    d=abs(p-q)
    xy=s*s-h2
    if d==0:
        return xy**low,-low*xy**(low-1) if low else F(0)
    a=sum((comb(d,2*j)*s**(d-2*j)*h2**j for j in range(d//2+1)),F(0))
    da=sum((j*comb(d,2*j)*s**(d-2*j)*h2**(j-1) for j in range(1,d//2+1)),F(0))
    return 2*xy**low*a,2*(xy**low*da-(low*xy**(low-1)*a if low else F(0)))

def branch(B,A,w,t,m):
    n=len(B)
    s=1-A*t
    h2=w*t**3
    out=[[F(0)]*n for _ in range(n)]
    der=[[F(0)]*n for _ in range(n)]
    cached={}
    for i,row in enumerate(B):
        for j,p in enumerate(row):
            for (px,py),c in p.items():
                if px<py:
                    continue
                if (px,py) not in cached:
                    cached[px,py]=branch_scalar(px,py,s,h2)
                value,dv=cached[px,py]
                out[i][j]+=c*value
                der[i][j]+=c*dv*t**3
    assert all(sum(row,F(0))==1 for row in out)
    assert all(sum(row,F(0))==0 for row in der)
    assert all(x>=0 for row in out for x in row)
    return out,der

def main():
    # Exact finite-word fractions exceed Python's default string digit cap.
    # Their generated numerators/denominators are intentional audit artifacts.
    sys.set_int_max_str_digits(0)
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    started=time.perf_counter()
    m=load_newton()
    h=m.load_helper()
    fa,pin=h.load_source(args.root)
    states=[h.representative(s,fa) for s in h.SHAPES6]
    index={s:i for i,s in enumerate(h.SHAPES6)}
    E=h.ordinary_polynomials(states,index,fa)
    B=h.bigon_polynomials(states,index,fa)
    A=m.INITIAL_A*9
    w=m.INITIAL_W*9
    t=F(1,1024)
    m.mp.mp.dps=120
    numeric_residual,J=m.evaluate(B,E,list(map(m.number,A)),list(map(m.number,w)),m.number(t))
    selected=m.mp.matrix([[J[i][j] for j in range(36)] for i in m.ROWS])
    r=m.mp.matrix([numeric_residual[i] for i in m.ROWS])
    D=m.mp.diag([m.number(x)**2 for x in w])
    dual=m.mp.lu_solve(selected*D*selected.T,-r)
    scale=max(abs(x) for x in dual)
    ell=[F(0)]*20
    for row,x in zip(m.ROWS,dual):
        ell[row]=F(m.mp.nstr(x/scale,100))
    # Exact source response and exact contracted derivatives. Four arm
    # matrices repeat, so their exact evaluation is shared, not approximated.
    cells=[branch(B,aa,ww,t,m) for aa,ww in zip(m.INITIAL_A,m.INITIAL_W)]
    factors=[ordinary(E,F(7,8))]
    gap_inner=ordinary(E,1-t)
    gap_outer=ordinary(E,F(9,10))
    variables=[]
    pair=F(7,8)
    for k in range(36):
        mat,der=cells[k%4]
        variables.append((len(factors),der))
        factors.append(mat)
        pair*=1-A[k]*t/2
        if k!=35:
            gap=F(9,10) if k%4==3 else 1-t
            factors.append(gap_outer if k%4==3 else gap_inner)
            pair*=gap
    calibration=F(1,4)/pair
    assert 0<calibration<1
    factors.append(ordinary(E,calibration))
    prefix=[[F(1)]+[F(0)]*19]
    for mat in factors:
        prefix.append(vm(prefix[-1],mat))
    suffix=[None]*(len(factors)+1)
    suffix[-1]=ell
    for k in range(len(factors)-1,-1,-1):
        suffix[k]=mv(factors[k],suffix[k+1])
    exact_residual=[x-y for x,y in zip(prefix[-1],ordinary(E,F(1,4))[0])]
    projections=[dot(vm(prefix[k],der),suffix[k+1]) for k,der in variables]
    lhs=abs(dot(ell,exact_residual))
    rhs=sum((ww*abs(v) for ww,v in zip(w,projections)),F(0))
    assert rhs>0 and lhs>rhs
    ratio=lhs/rhs
    # Exact integer comparison, exposing a simple strict certified bound.
    integer_bound=ratio.numerator//ratio.denominator
    assert integer_bound>1 and lhs>integer_bound*rhs
    result={"status":"EXACT_RATIONAL_LOCAL_LINEAR_RADIUS_OBSTRUCTION_EXECUTED",
            "source_sha256":pin,"executed_helper_sha256":m.HELPER_SHA,
            "executed_newton_provider_sha256":NEWTON_SHA,
            "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "source_word":"same initial strict36cellbank from ACTUAL-BANK-JACOBIAN-v2",
            "all20_exact_response_residual":list(map(str,exact_residual)),
            "rational_dual_covector_all20":list(map(str,ell)),
            "exact_dual_jacobian_columns_36":list(map(str,projections)),
            "abs_dual_residual":str(lhs),"sum_w_abs_dual_jacobian":str(rhs),
            "required_relative_infinity_radius_lower_bound_exact":str(ratio),
            "strict_integer_radius_lower_bound":integer_bound,
            "lower_bound_decimal":str(float(ratio)),
            "statement":"For every delta satisfying the complete initialbank linear Newton equation J*delta=-r, max_i(abs(delta_i)/w_i)>strict_integer_radius_lower_bound.",
            "proof":"|ell*r|=|sum_i(ell*J_i)*delta_i| <= rho*sum_i(w_i*|ell*J_i|); exact rational lhs>integer_bound*rhs.",
            "precision_used_only_to_propose_dual":120,"all_certificate_arithmetic":"fractions.Fraction",
            "runtime_seconds":time.perf_counter()-started,
            "not_claimed":["nonlinear source-fibre obstruction","all-positive one-sided large correction refusal",
                           "no ordinary source common zero","all-cap result","G4 master closure"]}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"strict_integer_radius_lower_bound":integer_bound,
                      "runtime_seconds":result["runtime_seconds"]}))
if __name__=="__main__":
    main()
