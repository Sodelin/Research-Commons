"""Second bounded common-zero route: actual weights AND positive placements.

The deterministic source product retains all chronological cross products.
The fixed physical weak scale is never shrunk to simulate a common zero.
"""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import argparse
import json
import time
import types

PROVIDER_SHA="a98763e657410860b6240538ec41a5e3659362707d1e0ebe85a49a82d150f3cb"
def load_provider():
    p=Path(__file__).with_name("bounded_common_zero.py")
    b=p.read_bytes()
    assert sha256(b).hexdigest()==PROVIDER_SHA
    m=types.ModuleType("frozen_actual_source_numeric_provider")
    m.__file__=str(p)
    exec(compile(b,str(p),"exec"),m.__dict__)
    return m

def ordinary_derivative(m,E,z):
    return [[m.mp.fsum(m.number(c)*e*z**(e-1) for e,c in p.items() if e) for p in row] for row in E]

def evaluate(m,B,E,A,w,gaps,t,jac=True):
    n=len(E)
    factors=[m.ordinary(E,m.number("7/8"))]
    derivatives=[]
    pair=m.number("7/8")
    for k in range(36):
        mat,der=m.branch(B,A[k],w[k],t)
        derivatives.append((len(factors),der,"weight",k))
        factors.append(mat)
        pair*=1-A[k]*t/2
        if k!=35:
            z=gaps[k]
            if not 0<z<1:
                raise ValueError("Nonpositive physical ordinary placement")
            derivatives.append((len(factors),ordinary_derivative(m,E,z),"gap",k))
            factors.append(m.ordinary(E,z))
            pair*=z
    calibration=m.number("1/4")/pair
    if not 0<calibration<1:
        raise ValueError("Final calibration is not a positive physical edge")
    factors.append(m.ordinary(E,calibration))
    v=[m.mp.mpf(1)]+[m.mp.mpf(0)]*(n-1)
    prefix=[v]
    for mat in factors:
        prefix.append(m.vm(prefix[-1],mat))
    target=m.ordinary(E,m.number("1/4"))[0]
    residual=[x-y for x,y in zip(prefix[-1],target)]
    if not jac:
        return residual,None
    suffix=[None]*(len(factors)+1)
    suffix[-1]=m.eye(n)
    for k in range(len(factors)-1,-1,-1):
        suffix[k]=m.mm(factors[k],suffix[k+1])
    dcal=m.vm(prefix[-2],ordinary_derivative(m,E,calibration))
    columns=[None]*71
    for pos,der,kind,k in derivatives:
        col=m.vm(m.vm(prefix[pos],der),suffix[pos+1])
        if kind=="weight":
            columns[k]=col
        else:
            columns[36+k]=[v-calibration/gaps[k]*d for v,d in zip(col,dcal)]
    return residual,[list(row) for row in zip(*columns)]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    started=time.perf_counter()
    m=load_provider()
    m.mp.mp.dps=120
    h=m.load_helper()
    fa,pin=h.load_source(args.root)
    states=[h.representative(s,fa) for s in h.SHAPES6]
    index={s:i for i,s in enumerate(h.SHAPES6)}
    E=h.ordinary_polynomials(states,index,fa)
    B=h.bigon_polynomials(states,index,fa)
    A=[m.number(a) for _ in range(9) for a in m.INITIAL_A]
    w=[m.number(b) for _ in range(9) for b in m.INITIAL_W]
    t=m.number("1/1024")
    gaps=[m.number("9/10") if k%4==3 else 1-t for k in range(35)]
    # Exact original bank control before changing source placements.
    first,_=evaluate(m,B,E,A,w,gaps,t,False)
    reference,_=m.evaluate(B,E,A,w,t,False)
    assert first==reference
    history=[]
    stop="bounded_three_steps_exhausted"
    for step in range(3):
        r,J=evaluate(m,B,E,A,w,gaps,t)
        mat=m.mp.matrix([[J[i][j] for j in range(71)] for i in m.ROWS])
        selected=m.mp.matrix([r[i] for i in m.ROWS])
        scale=w+[min(x,1-x) for x in gaps]
        D=m.mp.diag([x*x for x in scale])
        try:
            dual=m.mp.lu_solve(mat*D*mat.T,-selected)
            delta=D*mat.T*dual
        except (ValueError,ZeroDivisionError) as e:
            history.append({"step":step,"linear_solve_refusal":str(e)})
            stop="linear_solve_refused"
            break
        maximum=max(abs(delta[j])/scale[j] for j in range(71))
        alpha=m.mp.mpf(1)
        current=w+gaps
        for j in range(71):
            upper=min(A[j]**2/t,(1-A[j]*t)**2/t**3) if j<36 else m.mp.mpf(1)
            if delta[j]<0:
                alpha=min(alpha,m.mp.mpf("0.8")*current[j]/(-delta[j]))
            elif delta[j]>0:
                alpha=min(alpha,m.mp.mpf("0.8")*(upper-current[j])/delta[j])
        before=max(abs(x) for x in r)
        accepted=False
        for backtrack in range(5):
            candidate=[current[j]+alpha*delta[j] for j in range(71)]
            try:
                after_r,_=evaluate(m,B,E,A,candidate[:36],candidate[36:],t,False)
                after=max(abs(x) for x in after_r)
                if after<before:
                    accepted=True
                    break
            except ValueError:
                after=None
            alpha/=2
        entry={"step":step,"all20_residual_before":list(map(m.stringify,r)),
               "max_residual_before":m.stringify(before),"max_relative_safe_radius_step":m.stringify(maximum),
               "alpha":m.stringify(alpha),"accepted":accepted,"backtracks":backtrack,
               "linear_solve_residual":m.stringify(max(abs(x) for x in mat*delta+selected)),
               "max_residual_after":m.stringify(after) if after is not None else None,
               "full_weight_delta":list(map(m.stringify,delta[:36])),
               "full_placement_delta":list(map(m.stringify,delta[36:]))}
        history.append(entry)
        if not accepted or alpha<m.mp.mpf("1e-6"):
            stop="source_margin_or_contraction_gate_failed"
            break
        w,gaps=candidate[:36],candidate[36:]
    low,_=evaluate(m,B,E,A,w,gaps,t,False)
    saved_w=list(map(m.stringify,w))
    saved_gaps=list(map(m.stringify,gaps))
    m.mp.mp.dps=200
    A=[m.number(a) for _ in range(9) for a in m.INITIAL_A]
    w=list(map(m.mp.mpf,saved_w))
    gaps=list(map(m.mp.mpf,saved_gaps))
    t=m.number("1/1024")
    high,_=evaluate(m,B,E,A,w,gaps,t,False)
    result={"status":"BOUNDED_ACTUAL_WEIGHT_PLUS_PLACEMENT_COMMON_ZERO_GATE_ONLY",
            "original_source_sha256":pin,"executed_helper_sha256":m.HELPER_SHA,
            "executed_provider_sha256":PROVIDER_SHA,
            "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "target":"full labelled exchangeable cap-six E(1/4)","all20_rows_retained":True,
            "fixed_t":"1/1024","weight_variables":36,"ordinary_gap_variables":35,
            "exact_original_bank_layout_control":True,"pair_calibration_in_gap_derivative":True,
            "chronological_cross_products_preserved":True,"max_steps":3,"max_backtracks_per_step":5,
            "initial_dps":120,"replay_dps":200,"history":history,"stop_reason":stop,
            "saved_final_physical_w_decimal":saved_w,"saved_final_gap_survival_decimal":saved_gaps,
            "all20_final_residual":list(map(m.stringify,high)),
            "final_max_residual":m.stringify(max(abs(x) for x in high)),
            "precision_replay_disagreement":m.stringify(max(abs(x-m.mp.mpf(m.stringify(y))) for x,y in zip(high,low))),
            "runtime_seconds":time.perf_counter()-started,
            "not_claimed":["exact positive common zero","validated inverse theorem radius","all-cap budget","G4 master closure"]}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"stop_reason":stop,"steps":len(history),
                      "final_max_residual":result["final_max_residual"],"runtime_seconds":result["runtime_seconds"]}))
if __name__=="__main__":
    main()
