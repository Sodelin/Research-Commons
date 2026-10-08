"""One bounded continuation from the frozen positive-placement candidate."""
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
    module=types.ModuleType("frozen_placement_gate_provider")
    module.__file__=str(p)
    exec(compile(b,str(p),"exec"),module.__dict__)
    return module

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument("--candidate",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    started=time.perf_counter()
    g=load_provider()
    m=g.load_provider()
    m.mp.mp.dps=160
    raw=args.candidate.read_bytes()
    receipt=json.loads(raw)
    assert receipt["own_source_sha256"]==PROVIDER_SHA
    h=m.load_helper()
    fa,pin=h.load_source(args.root)
    states=[h.representative(s,fa) for s in h.SHAPES6]
    index={s:i for i,s in enumerate(h.SHAPES6)}
    E=h.ordinary_polynomials(states,index,fa)
    B=h.bigon_polynomials(states,index,fa)
    A=[m.number(a) for _ in range(9) for a in m.INITIAL_A]
    w=list(map(m.mp.mpf,receipt["saved_final_physical_w_decimal"]))
    gaps=list(map(m.mp.mpf,receipt["saved_final_gap_survival_decimal"]))
    t=m.number("1/1024")
    history=[]
    stop="predeclared_eight_steps_exhausted"
    for step in range(8):
        r,J=g.evaluate(m,B,E,A,w,gaps,t)
        before=max(abs(x) for x in r)
        if before<m.mp.mpf("1e-60"):
            stop="numerical_candidate_accuracy_reached_not_validated"
            break
        mat=m.mp.matrix([[J[i][j] for j in range(71)] for i in m.ROWS])
        selected=m.mp.matrix([r[i] for i in m.ROWS])
        scale=w+[min(x,1-x) for x in gaps]
        D=m.mp.diag([x*x for x in scale])
        try:
            delta=D*mat.T*m.mp.lu_solve(mat*D*mat.T,-selected)
        except (ValueError,ZeroDivisionError) as e:
            history.append({"step":step,"linear_solve_refusal":str(e)})
            stop="linear_solve_refused"
            break
        alpha=m.mp.mpf(1)
        current=w+gaps
        for j in range(71):
            upper=min(A[j]**2/t,(1-A[j]*t)**2/t**3) if j<36 else m.mp.mpf(1)
            if delta[j]<0:
                alpha=min(alpha,m.mp.mpf("0.8")*current[j]/(-delta[j]))
            elif delta[j]>0:
                alpha=min(alpha,m.mp.mpf("0.8")*(upper-current[j])/delta[j])
        accepted=False
        after=None
        for backtrack in range(8):
            candidate=[current[j]+alpha*delta[j] for j in range(71)]
            try:
                after_r,_=g.evaluate(m,B,E,A,candidate[:36],candidate[36:],t,False)
                after=max(abs(x) for x in after_r)
                if after<before:
                    accepted=True
                    break
            except ValueError:
                after=None
            alpha/=2
        history.append({"step":step,"all20_residual_before":[m.mp.nstr(x,150) for x in r],
                        "max_residual_before":m.mp.nstr(before,150),"max_residual_after":m.mp.nstr(after,150) if after else None,
                        "max_relative_safe_radius_step":m.mp.nstr(max(abs(delta[j])/scale[j] for j in range(71)),150),
                        "alpha":m.mp.nstr(alpha,150),"backtracks":backtrack,"accepted":accepted,
                        "minimum_weight_before":m.mp.nstr(min(w),150),
                        "minimum_gap_slack_before":m.mp.nstr(min(min(x,1-x) for x in gaps),150),
                        "linear_solve_residual":m.mp.nstr(max(abs(x) for x in mat*delta+selected),150)})
        if not accepted or alpha<m.mp.mpf("1e-6"):
            stop="strict_source_margin_or_contraction_gate_failed"
            break
        w,gaps=candidate[:36],candidate[36:]
    low,_=g.evaluate(m,B,E,A,w,gaps,t,False)
    saved_w=[m.mp.nstr(x,150) for x in w]
    saved_gaps=[m.mp.nstr(x,150) for x in gaps]
    m.mp.mp.dps=240
    A=[m.number(a) for _ in range(9) for a in m.INITIAL_A]
    w=list(map(m.mp.mpf,saved_w))
    gaps=list(map(m.mp.mpf,saved_gaps))
    t=m.number("1/1024")
    high,_=g.evaluate(m,B,E,A,w,gaps,t,False)
    result={"status":"BOUNDED_ACTUAL_SOURCE_PLACEMENT_CONTINUATION_ONLY",
            "original_source_sha256":pin,"executed_placement_provider_sha256":PROVIDER_SHA,
            "initial_candidate_sha256":sha256(raw).hexdigest(),
            "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "fixed_target":"all20 cap-six forest rows E(1/4)","fixed_physical_t":"1/1024",
            "max_steps":8,"max_backtracks_per_step":8,"working_digits":160,"replay_digits":240,
            "history":history,"stop_reason":stop,"all20_final_residual":[m.mp.nstr(x,150) for x in high],
            "final_max_residual":m.mp.nstr(max(abs(x) for x in high),150),
            "precision_replay_disagreement":m.mp.nstr(max(abs(x-m.mp.mpf(m.mp.nstr(y,150))) for x,y in zip(high,low)),150),
            "saved_final_physical_w_decimal":saved_w,"saved_final_gap_survival_decimal":saved_gaps,
            "all_source_factors_remain_strict":True,"full_chronological_product_retained":True,
            "runtime_seconds":time.perf_counter()-started,
            "not_claimed":["exact ordinary common zero","validated radius","all-cap budget","G4 master closure"]}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"steps":len(history),"stop_reason":stop,
                      "final_max_residual":result["final_max_residual"],"runtime_seconds":result["runtime_seconds"]}))
if __name__=="__main__":
    main()
