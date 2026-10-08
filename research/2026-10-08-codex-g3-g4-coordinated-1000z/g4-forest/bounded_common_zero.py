"""Bounded high-precision Newton gate on the actual complete forest source.

All weights belong to one deterministic physical word. This is numerical
candidate discovery/failure evidence, never a validated common-zero proof.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import time
import types
import mpmath as mp

HELPER_SHA="e0ced6748fd6fbe27f8165446a1c63a09bdb598fd1bdcd89115d4ae4853193b8"
ROWS=[0,1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,17,18]
INITIAL_A=[F(i,5) for i in range(1,5)]
INITIAL_W=[F(2,125),F(33,1000),F(49,750),F(19,1000)]

def load_helper():
    p=Path(__file__).with_name("exact_forest_layer.py")
    b=p.read_bytes()
    assert sha256(b).hexdigest()==HELPER_SHA
    m=types.ModuleType("authenticated_forest_layer")
    m.__file__=str(p)
    exec(compile(b,str(p),"exec"),m.__dict__)
    return m
def number(q):
    q=F(q)
    return mp.mpf(q.numerator)/q.denominator
def zeros(n):
    return [[mp.mpf(0)]*n for _ in range(n)]
def eye(n):
    return [[mp.mpf(i==j) for j in range(n)] for i in range(n)]
def mm(a,b):
    n=len(a)
    out=zeros(n)
    for i,row in enumerate(a):
        for k,c in enumerate(row):
            if c:
                for j,d in enumerate(b[k]):
                    if d:
                        out[i][j]+=c*d
    return out
def vm(v,a):
    out=[mp.mpf(0)]*len(v)
    for k,c in enumerate(v):
        if c:
            for j,d in enumerate(a[k]):
                if d:
                    out[j]+=c*d
    return out
def ordinary(E,z):
    return [[mp.fsum(number(c)*z**e for e,c in p.items()) for p in row] for row in E]
def branch_scalar(p,q,s,h2):
    m=min(p,q)
    d=abs(p-q)
    xy=s*s-h2
    if d==0:
        return xy**m,-m*xy**(m-1) if m else mp.mpf(0)
    a=mp.fsum(comb(d,2*j)*s**(d-2*j)*h2**j for j in range(d//2+1))
    da=mp.fsum(j*comb(d,2*j)*s**(d-2*j)*h2**(j-1) for j in range(1,d//2+1))
    return 2*xy**m*a,2*(xy**m*da-(m*xy**(m-1)*a if m else 0))
def branch(B,A,w,t):
    n=len(B)
    s=1-A*t
    h2=w*t**3
    if not (w>0 and h2<s*s and h2<(A*t)**2):
        raise ValueError("Not a strict original source arm")
    out=zeros(n)
    der=zeros(n)
    cached={}
    for i,row in enumerate(B):
        for j,p in enumerate(row):
            for (px,py),c in p.items():
                if px<py:
                    continue
                if (px,py) not in cached:
                    cached[px,py]=branch_scalar(px,py,s,h2)
                v,dv=cached[px,py]
                out[i][j]+=number(c)*v
                der[i][j]+=number(c)*dv*t**3
    return out,der

def evaluate(B,E,A,w,t,need_jacobian=True):
    n=len(E)
    factors=[ordinary(E,number(F(7,8)))]
    derivatives=[]
    pair=number(F(7,8))
    for k,(aa,ww) in enumerate(zip(A,w)):
        mat,der=branch(B,aa,ww,t)
        derivatives.append((len(factors),der))
        factors.append(mat)
        pair*=1-aa*t/2
        if k!=35:
            gap=number(F(9,10)) if k%4==3 else 1-t
            factors.append(ordinary(E,gap))
            pair*=gap
    calibration=number(F(1,4))/pair
    if not 0<calibration<1:
        raise ValueError("Final original ordinary calibration is not strict")
    factors.append(ordinary(E,calibration))
    v=[mp.mpf(1)]+[mp.mpf(0)]*(n-1)
    prefix=[v]
    for mat in factors:
        prefix.append(vm(prefix[-1],mat))
    target=ordinary(E,number(F(1,4)))[0]
    residual=[x-y for x,y in zip(prefix[-1],target)]
    if not need_jacobian:
        return residual,None
    suffix=[None]*(len(factors)+1)
    suffix[-1]=eye(n)
    for k in range(len(factors)-1,-1,-1):
        suffix[k]=mm(factors[k],suffix[k+1])
    columns=[vm(vm(prefix[k],der),suffix[k+1]) for k,der in derivatives]
    return residual,[list(row) for row in zip(*columns)]

def stringify(x):
    return mp.nstr(x,100)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument("--output",type=Path,required=True)
    ap.add_argument("--steps",type=int,default=3)
    ap.add_argument("--dps",type=int,default=120)
    args=ap.parse_args()
    assert 1<=args.steps<=4 and args.dps>=100
    started=time.perf_counter()
    mp.mp.dps=args.dps
    h=load_helper()
    fa,pin=h.load_source(args.root)
    states=[h.representative(s,fa) for s in h.SHAPES6]
    index={s:i for i,s in enumerate(h.SHAPES6)}
    E=h.ordinary_polynomials(states,index,fa)
    B=h.bigon_polynomials(states,index,fa)
    A=[number(a) for _ in range(9) for a in INITIAL_A]
    w=[number(b) for _ in range(9) for b in INITIAL_W]
    t=number(F(1,1024))
    history=[]
    initial_residual=None
    stop="bounded_steps_exhausted"
    for step in range(args.steps):
        residual,J=evaluate(B,E,A,w,t)
        if initial_residual is None:
            initial_residual=residual[:]
        selected=mp.matrix([[J[i][j] for j in range(36)] for i in ROWS])
        r=mp.matrix([residual[i] for i in ROWS])
        # Minimum relative-weight Euclidean correction, an explicit right
        # inverse using all36 original physical weights. No probability mixture.
        D=mp.diag([x*x for x in w])
        try:
            dual=mp.lu_solve(selected*D*selected.T,-r)
            delta=D*selected.T*dual
        except (ZeroDivisionError,ValueError) as e:
            stop="high_precision_linear_solve_refused"
            history.append({"step":step,"reason":str(e)})
            break
        rel=max(abs(delta[j])/w[j] for j in range(36))
        alpha=mp.mpf(1)
        for j in range(36):
            upper=min(A[j]**2/t,(1-A[j]*t)**2/t**3)
            if delta[j]<0:
                alpha=min(alpha,mp.mpf("0.8")*w[j]/(-delta[j]))
            elif delta[j]>0:
                alpha=min(alpha,mp.mpf("0.8")*(upper-w[j])/delta[j])
        linear_error=max(abs(x) for x in (selected*delta+r))
        before=max(abs(x) for x in residual)
        candidate=[w[j]+alpha*delta[j] for j in range(36)]
        after_residual,_=evaluate(B,E,A,candidate,t,False)
        after=max(abs(x) for x in after_residual)
        entry={"step":step,"all20_residual_before":list(map(stringify,residual)),
               "all20_max_before":stringify(before),"full_newton_delta_w":list(map(stringify,delta)),
               "max_relative_weight_correction":stringify(rel),"positivity_preserving_alpha":stringify(alpha),
               "linear_solve_residual":stringify(linear_error),"all20_max_after":stringify(after),
               "minimum_weight_after":stringify(min(candidate)),"strict_source_after":True}
        history.append(entry)
        # Bounded gate: do not chase a noncontracting or extremely damped bank.
        if after>=before or alpha<mp.mpf("1e-6"):
            stop="local_newton_gate_failed_margin_or_contraction"
            break
        w=candidate
    final_residual,_=evaluate(B,E,A,w,t,False)
    # Independent precision replay of the SAME saved decimal physical weights.
    saved_w=list(map(stringify,w))
    low_final=list(map(stringify,final_residual))
    mp.mp.dps=args.dps+80
    A=[number(a) for _ in range(9) for a in INITIAL_A]
    w=[mp.mpf(x) for x in saved_w]
    t=number(F(1,1024))
    high_residual,_=evaluate(B,E,A,w,t,False)
    replay_disagreement=max(abs(x-mp.mpf(y)) for x,y in zip(high_residual,low_final))
    result={"status":"BOUNDED_ACTUAL_SOURCE_NUMERICAL_COMMON_ZERO_GATE_ONLY",
            "source_sha256":pin,"executed_helper_sha256":HELPER_SHA,
            "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "mpmath_version":mp.__version__,"initial_precision_digits":args.dps,
            "replay_precision_digits":args.dps+80,"predeclared_max_steps":args.steps,
            "target":"complete exchangeable labelled cap-six E(1/4), mass and pairfixed",
            "all20_rows_used_for_residual":True,"square_coordinate_rows":ROWS,
            "one_original_physical_weight_vector_all_arities":True,"deterministic_word_cells":36,
            "initial_w_four_repeated_nine_times":list(map(str,INITIAL_W)),
            "A_four_repeated_nine_times":list(map(str,INITIAL_A)),"t":"1/1024",
            "history":history,"stop_reason":stop,"saved_final_physical_w_decimal":saved_w,
            "all20_final_residual":list(map(stringify,high_residual)),
            "final_max_residual":stringify(max(abs(x) for x in high_residual)),
            "precision_replay_max_disagreement":stringify(replay_disagreement),
            "runtime_seconds":time.perf_counter()-started,
            "not_claimed":["exact common zero","interval validated inverse/radius","ordinary source interior",
                           "all-cap uniform hazard","G4 fixed-target master closure"]}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"steps":len(history),"stop_reason":stop,
                      "final_max_residual":result["final_max_residual"],
                      "runtime_seconds":result["runtime_seconds"]}))
if __name__=="__main__":
    main()
