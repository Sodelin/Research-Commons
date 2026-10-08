"""Bounded full-forest source centering with free actual arm means/contrasts."""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
from math import comb
import argparse
import json
import time
import types

FIXED_PROVIDER_SHA="9f3656c9122a10e46aa4e62555a73e5167e0f1a5127394d76ac76b7ca011cf29"
CANDIDATE_SHA="79e79e7b2add096ecb67aab16498a74c3d696ee8b5ed2d6a3d7aa7e41e71bb2f"
def load_fixed():
    p=Path(__file__).with_name("fixed_hazard_gate.py")
    b=p.read_bytes()
    assert sha256(b).hexdigest()==FIXED_PROVIDER_SHA
    f=types.ModuleType("frozen_fixed_hazard_source_provider")
    f.__file__=str(p)
    exec(compile(b,str(p),"exec"),f.__dict__)
    return f

def mean_derivative(m,B,A,w,t):
    s=1-A*t
    h2=w*t**3
    xy=s*s-h2
    n=len(B)
    out=m.zeros(n)
    cached={}
    for i,row in enumerate(B):
        for j,p in enumerate(row):
            for (px,py),c in p.items():
                if px<py:
                    continue
                if (px,py) not in cached:
                    low=py
                    diff=px-py
                    if diff==0:
                        ds=2*low*s*xy**(low-1) if low else m.mp.mpf(0)
                    else:
                        v=m.mp.fsum(comb(diff,2*k)*s**(diff-2*k)*h2**k for k in range(diff//2+1))
                        dv=m.mp.fsum((diff-2*k)*comb(diff,2*k)*s**(diff-2*k-1)*h2**k for k in range(diff//2+1) if diff>2*k)
                        ds=2*((2*low*s*xy**(low-1)*v if low else 0)+xy**low*dv)
                    cached[px,py]=-t*ds
                out[i][j]+=m.number(c)*cached[px,py]
    return out

def evaluate(f,g,m,B,E,A,w,theta,H,t,jac=True):
    hazards,gaps=f.allocation(m,theta,H)
    factors=[m.ordinary(E,m.number("7/8"))]
    derivatives=[]
    pair=m.number("7/8")*m.mp.exp(-H)
    for k in range(36):
        mat,der=m.branch(B,A[k],w[k],t)
        derivatives.append((len(factors),der,"weight",k))
        derivatives.append((len(factors),mean_derivative(m,B,A[k],w[k],t),"mean",k))
        factors.append(mat)
        pair*=1-A[k]*t/2
        if k!=35:
            derivatives.append((len(factors),g.ordinary_derivative(m,E,gaps[k]),"gap",k))
            factors.append(m.ordinary(E,gaps[k]))
    calibration=m.number("1/4")/pair
    if not 0<calibration<1:
        raise ValueError("The actual final calibration is not strict")
    factors.append(m.ordinary(E,calibration))
    prefix=[[m.mp.mpf(1)]+[m.mp.mpf(0)]*19]
    for mat in factors:
        prefix.append(m.vm(prefix[-1],mat))
    target=m.ordinary(E,m.number("1/4"))[0]
    residual=[x-y for x,y in zip(prefix[-1],target)]
    if not jac:
        return residual,None,hazards,gaps,calibration
    suffix=[None]*(len(factors)+1)
    suffix[-1]=m.eye(20)
    for k in range(len(factors)-1,-1,-1):
        suffix[k]=m.mm(factors[k],suffix[k+1])
    dcal=m.vm(prefix[-2],g.ordinary_derivative(m,E,calibration))
    weights=[None]*36
    means=[None]*36
    placements=[None]*35
    for pos,der,kind,k in derivatives:
        col=m.vm(m.vm(prefix[pos],der),suffix[pos+1])
        if kind=="weight":
            weights[k]=col
        elif kind=="mean":
            means[k]=[x+calibration*t/(2*(1-A[k]*t/2))*d for x,d in zip(col,dcal)]
        else:
            placements[k]=[x-calibration/gaps[k]*d for x,d in zip(col,dcal)]
    out=[]
    for i in range(20):
        row=[v[i] for v in weights]+[v[i] for v in means]
        total=m.mp.fsum(hazards[k]*gaps[k]*placements[k][i] for k in range(35))
        row += [-hazards[j]*gaps[j]*placements[j][i]+hazards[j]/H*total for j in range(34)]
        out.append(row)
    return residual,out,hazards,gaps,calibration

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    started=time.perf_counter()
    f=load_fixed()
    g=f.load_provider()
    m=g.load_provider()
    m.mp.mp.dps=160
    h=m.load_helper()
    fa,pin=h.load_source(args.root)
    states=[h.representative(s,fa) for s in h.SHAPES6]
    index={s:i for i,s in enumerate(h.SHAPES6)}
    E=h.ordinary_polynomials(states,index,fa)
    B=h.bigon_polynomials(states,index,fa)
    cp=Path(__file__).with_name("FIXED-HAZARD-GATE.json")
    raw=cp.read_bytes()
    assert sha256(raw).hexdigest()==CANDIDATE_SHA
    receipt=json.loads(raw)
    A=[m.number(a) for _ in range(9) for a in m.INITIAL_A]
    w=list(map(m.mp.mpf,receipt["saved_final_w_decimal"]))
    theta=list(map(m.mp.mpf,receipt["saved_final_allocation_logits_decimal"]))
    t=m.number("1/1024")
    H=8*(-m.mp.log(m.number("9/10")))+27*(-m.mp.log(1-t))
    # Compare the new mean-control source chart to the frozen fixed-A source.
    first,_,_,_,_=evaluate(f,g,m,B,E,A,w,theta,H,t,False)
    reference,_,_,_=f.evaluate(g,m,B,E,A,w,theta,H,t,False)
    baseline_disagreement=max(abs(x-y) for x,y in zip(first,reference))
    assert baseline_disagreement<m.mp.mpf("1e-150")
    history=[]
    stop="predeclared_five_steps_exhausted"
    for step in range(5):
        r,J,hazards,gaps,cal=evaluate(f,g,m,B,E,A,w,theta,H,t)
        before=max(abs(x) for x in r)
        if before<m.mp.mpf("1e-60"):
            stop="numerical_candidate_accuracy_reached_not_validated"
            break
        mat=m.mp.matrix([[J[i][j] for j in range(106)] for i in m.ROWS])
        selected=m.mp.matrix([r[i] for i in m.ROWS])
        scales=w+A+[m.mp.mpf(1)]*34
        D=m.mp.diag([x*x for x in scales])
        try:
            delta=D*mat.T*m.mp.lu_solve(mat*D*mat.T,-selected)
        except (ZeroDivisionError,ValueError) as e:
            history.append({"step":step,"linear_solve_refusal":str(e)})
            stop="linear_solve_refused"
            break
        alpha=m.mp.mpf(1)
        for j in range(36):
            if delta[j]<0:
                alpha=min(alpha,m.mp.mpf("0.8")*w[j]/(-delta[j]))
            margin=A[j]-m.mp.sqrt(w[j]*t)
            if delta[36+j]<0:
                alpha=min(alpha,m.mp.mpf("0.8")*margin/(-delta[36+j]))
        logit_change=max(abs(delta[j]) for j in range(72,106))
        if logit_change:
            alpha=min(alpha,m.mp.mpf(4)/logit_change)
        accepted=False
        after=None
        for backtrack in range(10):
            nw=[w[j]+alpha*delta[j] for j in range(36)]
            na=[A[j]+alpha*delta[36+j] for j in range(36)]
            nt=[theta[j]+alpha*delta[72+j] for j in range(34)]
            try:
                rr,_,_,_,_=evaluate(f,g,m,B,E,na,nw,nt,H,t,False)
                after=max(abs(x) for x in rr)
                if after<before:
                    accepted=True
                    break
            except ValueError:
                after=None
            alpha/=2
        history.append({"step":step,"all20_residual_before":[m.mp.nstr(x,150) for x in r],
                        "max_residual_before":m.mp.nstr(before,150),"max_residual_after":m.mp.nstr(after,150) if after else None,
                        "alpha":m.mp.nstr(alpha,150),"accepted":accepted,"backtracks":backtrack,
                        "max_relative_weight_step":m.mp.nstr(max(abs(delta[j])/w[j] for j in range(36)),150),
                        "max_relative_mean_step":m.mp.nstr(max(abs(delta[36+j])/A[j] for j in range(36)),150),
                        "max_logit_step":m.mp.nstr(logit_change,150),"calibration_survival":m.mp.nstr(cal,150),
                        "linear_solve_residual":m.mp.nstr(max(abs(x) for x in mat*delta+selected),150)})
        if not accepted or alpha<m.mp.mpf("1e-6"):
            stop="strict_source_margin_or_contraction_gate_failed"
            break
        w,A,theta=nw,na,nt
    low,_,_,_,_=evaluate(f,g,m,B,E,A,w,theta,H,t,False)
    saved_A=[m.mp.nstr(x,150) for x in A]
    saved_w=[m.mp.nstr(x,150) for x in w]
    saved_theta=[m.mp.nstr(x,150) for x in theta]
    m.mp.mp.dps=240
    t=m.number("1/1024")
    H=8*(-m.mp.log(m.number("9/10")))+27*(-m.mp.log(1-t))
    high,_,_,gaps,cal=evaluate(f,g,m,B,E,list(map(m.mp.mpf,saved_A)),list(map(m.mp.mpf,saved_w)),list(map(m.mp.mpf,saved_theta)),H,t,False)
    result={"status":"BOUNDED_ORIGINAL_ARM_MEAN_CONTRAST_AND_FIXED_CONNECTOR_HAZARD_GATE_ONLY",
            "original_source_sha256":pin,"executed_fixed_provider_sha256":FIXED_PROVIDER_SHA,
            "initial_candidate_sha256":CANDIDATE_SHA,"own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "fixed_target":"all20 cap-six original forest rows E(1/4)","fixed_weak_t":"1/1024",
            "mean_variables":36,"contrast_weight_variables":36,"fixed_total_hazard_logits":34,
            "source_fair_independent_current_root_route":True,"A_pair_calibration_derivative_retained":True,
            "fixed_total_connector_hazard":True,"all_chronological_cross_products_retained":True,
            "baseline_frozen_source_chart_control":True,"baseline_source_chart_disagreement":m.mp.nstr(baseline_disagreement,150),
            "max_steps":5,"max_backtracks_per_step":10,
            "working_digits":160,"replay_digits":240,"history":history,"stop_reason":stop,
            "saved_final_A_decimal":saved_A,"saved_final_w_decimal":saved_w,
            "saved_final_allocation_logits_decimal":saved_theta,"saved_final_gap_survivals_decimal":[m.mp.nstr(x,150) for x in gaps],
            "final_calibration_survival":m.mp.nstr(cal,150),"all20_final_residual":[m.mp.nstr(x,150) for x in high],
            "final_max_residual":m.mp.nstr(max(abs(x) for x in high),150),
            "precision_replay_disagreement":m.mp.nstr(max(abs(x-m.mp.mpf(m.mp.nstr(y,150))) for x,y in zip(high,low)),150),
            "runtime_seconds":time.perf_counter()-started,
            "not_claimed":["exact positive common zero","validated inverse/radius","all-cap finitebudget","G4 master closure"]}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"steps":len(history),"stop_reason":stop,
                      "final_max_residual":result["final_max_residual"],"runtime_seconds":result["runtime_seconds"]}))
if __name__=="__main__":
    main()
