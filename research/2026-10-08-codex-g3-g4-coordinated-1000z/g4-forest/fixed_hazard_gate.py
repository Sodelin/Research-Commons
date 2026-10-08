"""Bounded physical common-zero gate with fixed total connector hazard.

Thirty-four logits allocate one positive fixed hazard among35ordinarygaps;
the last logit is fixed. This keeps the final positive calibration reserve.
The fixed weak scale and all chronological source forest rows are retained.
"""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import argparse
import json
import time
import types

PROVIDER_SHA="6887328e6c14297557eadbb37656dd364f55eec8e2a691ea7b5cea69a188eb02"
def load_provider():
    p=Path(__file__).with_name("bounded_placement_gate.py")
    b=p.read_bytes()
    assert sha256(b).hexdigest()==PROVIDER_SHA
    g=types.ModuleType("frozen_placement_source_provider")
    g.__file__=str(p)
    exec(compile(b,str(p),"exec"),g.__dict__)
    return g

def allocation(m,theta,H):
    z=theta+[m.mp.mpf(0)]
    offset=max(z)
    exp=[m.mp.exp(x-offset) for x in z]
    total=m.mp.fsum(exp)
    hazards=[H*x/total for x in exp]
    return hazards,[m.mp.exp(-x) for x in hazards]

def evaluate(g,m,B,E,A,w,theta,H,t,jac=True):
    hazards,gaps=allocation(m,theta,H)
    r,J=g.evaluate(m,B,E,A,w,gaps,t,jac)
    if not jac:
        return r,None,hazards,gaps
    n=len(r)
    transformed=[row[:36] for row in J]
    for i in range(n):
        total=m.mp.fsum(hazards[k]*gaps[k]*J[i][36+k] for k in range(35))
        for j in range(34):
            transformed[i].append(-hazards[j]*gaps[j]*J[i][36+j]+hazards[j]/H*total)
    return r,transformed,hazards,gaps

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    started=time.perf_counter()
    g=load_provider()
    m=g.load_provider()
    m.mp.mp.dps=160
    h=m.load_helper()
    fa,pin=h.load_source(args.root)
    states=[h.representative(s,fa) for s in h.SHAPES6]
    index={s:i for i,s in enumerate(h.SHAPES6)}
    E=h.ordinary_polynomials(states,index,fa)
    B=h.bigon_polynomials(states,index,fa)
    A=[m.number(a) for _ in range(9) for a in m.INITIAL_A]
    w=[m.number(b) for _ in range(9) for b in m.INITIAL_W]
    t=m.number("1/1024")
    initial_gaps=[m.number("9/10") if k%4==3 else 1-t for k in range(35)]
    initial_h=[-m.mp.log(z) for z in initial_gaps]
    H=m.mp.fsum(initial_h)
    theta=[m.mp.log(x/initial_h[-1]) for x in initial_h[:-1]]
    initial_pair=m.number("7/8")*m.mp.exp(-H)
    for a in A:
        initial_pair*=1-a*t/2
    calibration=m.number("1/4")/initial_pair
    assert 0<calibration<1
    baseline,_=m.evaluate(B,E,A,w,t,False)
    first,_,_,_=evaluate(g,m,B,E,A,w,theta,H,t,False)
    assert max(abs(x-y) for x,y in zip(first,baseline))<m.mp.mpf("1e-150")
    history=[]
    stop="predeclared_five_steps_exhausted"
    for step in range(5):
        r,J,hazards,gaps=evaluate(g,m,B,E,A,w,theta,H,t)
        before=max(abs(x) for x in r)
        if before<m.mp.mpf("1e-60"):
            stop="numerical_candidate_accuracy_reached_not_validated"
            break
        mat=m.mp.matrix([[J[i][j] for j in range(70)] for i in m.ROWS])
        selected=m.mp.matrix([r[i] for i in m.ROWS])
        scales=w+[m.mp.mpf(1)]*34
        D=m.mp.diag([x*x for x in scales])
        try:
            delta=D*mat.T*m.mp.lu_solve(mat*D*mat.T,-selected)
        except (ValueError,ZeroDivisionError) as e:
            history.append({"step":step,"linear_solve_refusal":str(e)})
            stop="linear_solve_refused"
            break
        alpha=m.mp.mpf(1)
        for j in range(36):
            upper=min(A[j]**2/t,(1-A[j]*t)**2/t**3)
            if delta[j]<0:
                alpha=min(alpha,m.mp.mpf("0.8")*w[j]/(-delta[j]))
            elif delta[j]>0:
                alpha=min(alpha,m.mp.mpf("0.8")*(upper-w[j])/delta[j])
        logit_change=max(abs(delta[j]) for j in range(36,70))
        if logit_change:
            alpha=min(alpha,m.mp.mpf(4)/logit_change)
        accepted=False
        after=None
        for backtrack in range(8):
            new_w=[w[j]+alpha*delta[j] for j in range(36)]
            new_theta=[theta[j]+alpha*delta[36+j] for j in range(34)]
            try:
                rr,_,_,_=evaluate(g,m,B,E,A,new_w,new_theta,H,t,False)
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
                        "max_logit_step":m.mp.nstr(logit_change,150),
                        "minimum_positive_gap_hazard":m.mp.nstr(min(hazards),150),
                        "fixed_hazard_sum_error":m.mp.nstr(abs(m.mp.fsum(hazards)-H),150),
                        "linear_solve_residual":m.mp.nstr(max(abs(x) for x in mat*delta+selected),150)})
        if not accepted or alpha<m.mp.mpf("1e-6"):
            stop="strict_weight_margin_or_contraction_gate_failed"
            break
        w,theta=new_w,new_theta
    low,_,_,_=evaluate(g,m,B,E,A,w,theta,H,t,False)
    saved_w=[m.mp.nstr(x,150) for x in w]
    saved_theta=[m.mp.nstr(x,150) for x in theta]
    m.mp.mp.dps=240
    A=[m.number(a) for _ in range(9) for a in m.INITIAL_A]
    t=m.number("1/1024")
    initial_gaps=[m.number("9/10") if k%4==3 else 1-t for k in range(35)]
    H=m.mp.fsum(-m.mp.log(z) for z in initial_gaps)
    high,_,hazards,gaps=evaluate(g,m,B,E,A,list(map(m.mp.mpf,saved_w)),list(map(m.mp.mpf,saved_theta)),H,t,False)
    result={"status":"BOUNDED_FIXED_TOTAL_CONNECTOR_HAZARD_SOURCE_ZERO_GATE_ONLY",
            "original_source_sha256":pin,"executed_provider_sha256":PROVIDER_SHA,
            "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "target":"complete labelled cap-six E(1/4)","fixed_weak_t":"1/1024",
            "independent_weight_variables":36,"independent_hazard_allocation_logits":34,
            "last_gap_dependent_via_positive_softmax":True,"connector_total_hazard":"8*(-log(9/10))+27*(-log(1023/1024))",
            "final_calibration_reserve_is_constant":True,"initial_final_calibration_survival":m.mp.nstr(calibration,150),
            "actual_b2_independent_w":True,"all_chronological_cross_products_retained":True,
            "original_baseline_layout_control":True,"max_steps":5,"max_backtracks_per_step":8,
            "max_accepted_logit_move_per_step":4,"working_digits":160,"replay_digits":240,
            "history":history,"stop_reason":stop,"saved_final_w_decimal":saved_w,
            "saved_final_allocation_logits_decimal":saved_theta,"saved_final_gap_survivals_decimal":[m.mp.nstr(x,150) for x in gaps],
            "all20_final_residual":[m.mp.nstr(x,150) for x in high],
            "final_max_residual":m.mp.nstr(max(abs(x) for x in high),150),
            "precision_replay_disagreement":m.mp.nstr(max(abs(x-m.mp.mpf(m.mp.nstr(y,150))) for x,y in zip(high,low)),150),
            "runtime_seconds":time.perf_counter()-started,
            "not_claimed":["exact positive common zero","interval validated radius","all-cap budget","G4 master closure"]}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"steps":len(history),"stop_reason":stop,
                      "final_max_residual":result["final_max_residual"],"runtime_seconds":result["runtime_seconds"]}))
if __name__=="__main__":
    main()
