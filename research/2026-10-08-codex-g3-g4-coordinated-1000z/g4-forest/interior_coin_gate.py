"""Bounded complete source gate with original interior inheritance controls."""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import comb
import argparse,json,time,types

FIXED_SHA="9f3656c9122a10e46aa4e62555a73e5167e0f1a5127394d76ac76b7ca011cf29"
def load_fixed():
    p=Path(__file__).with_name("fixed_hazard_gate.py");b=p.read_bytes()
    assert sha256(b).hexdigest()==FIXED_SHA
    f=types.ModuleType("frozen_fixed_hazard_provider");f.__file__=str(p)
    exec(compile(b,str(p),"exec"),f.__dict__);return f

def full_source_polynomials(states,index,fa,h):
    n=len(states);out=[[{} for _ in range(n)] for _ in range(n)]
    for i,f in enumerate(states):
        k=len(f)
        for bits in product((0,1),repeat=k):
            aa=tuple(j for j in range(k) if bits[j]==0);bb=tuple(j for j in range(k) if bits[j]==1)
            for va,pa in fa.edge_polynomials(len(aa)).items():
                ga=tuple(fa.relabel(t,dict(enumerate(aa))) for t in va)
                for vb,pb in fa.edge_polynomials(len(bb)).items():
                    gb=tuple(fa.relabel(t,dict(enumerate(bb))) for t in vb)
                    j=index[h.forest_shape(fa.graft(f,fa.forest(ga+gb)))]
                    for px,cx in pa.items():
                        for py,cy in pb.items():
                            for l in range(len(bb)+1):
                                h.p_add(out[i][j],(px,py,len(aa)+l),cx*cy*(-1)**l*comb(len(bb),l))
    return out

def cell(m,B,a,w,g,t,jac):
    s=1-a*t;h2=w*t**3
    if not(0<s<1 and 0<h2<min(s*s,(1-s)**2) and m.mp.mpf("0.25")<g<m.mp.mpf("0.75")):
        raise ValueError("Original strict source domain or prescribed coin interval")
    h=m.mp.sqrt(h2);x=s-h;y=s+h;dh=t**3/(2*h)
    xp=[x**j for j in range(16)];yp=[y**j for j in range(16)];gp=[g**j for j in range(7)]
    value=m.zeros(20);da=m.zeros(20);dw=m.zeros(20);dg=m.zeros(20)
    for i,row in enumerate(B):
        for j,p in enumerate(row):
            for (px,py,pg),c0 in p.items():
                c=m.number(c0);base=c*xp[px]*yp[py]*gp[pg];value[i][j]+=base
                if jac:
                    dx=c*px*xp[px-1]*yp[py]*gp[pg] if px else 0
                    dy=c*py*xp[px]*yp[py-1]*gp[pg] if py else 0
                    da[i][j]+=-t*(dx+dy);dw[i][j]+=dh*(-dx+dy)
                    if pg:dg[i][j]+=c*pg*xp[px]*yp[py]*gp[pg-1]
    q=g*g*x+(1-g)**2*y+2*g*(1-g)
    dq=[(1-2*g)*dh,-t*(g*g+(1-g)**2),2*g*(x-1)-2*(1-g)*(y-1)]
    return value,[dw,da,dg],q,dq

def evaluate(f,gp,m,B,E,A,w,coin,theta,H,t,jac=True):
    hazards,gaps=f.allocation(m,theta,H)
    factors=[m.ordinary(E,m.number("7/8"))];derivatives=[];pair=m.number("7/8")*m.mp.exp(-H)
    for k in range(36):
        mat,ds,q,dq=cell(m,B,A[k],w[k],coin[k],t,jac)
        if jac:
            for z in range(3):derivatives.append((len(factors),ds[z],z*36+k,-dq[z]/q))
        factors.append(mat);pair*=q
        if k!=35:
            if jac:derivatives.append((len(factors),gp.ordinary_derivative(m,E,gaps[k]),108+k,-1/gaps[k]))
            factors.append(m.ordinary(E,gaps[k]))
    calibration=m.number("1/4")/pair
    if not 0<calibration<1:raise ValueError("Final calibration is not positive")
    factors.append(m.ordinary(E,calibration))
    prefix=[[m.mp.mpf(1)]+[m.mp.mpf(0)]*19]
    for mat in factors:prefix.append(m.vm(prefix[-1],mat))
    target=m.ordinary(E,m.number("1/4"))[0];r=[x-y for x,y in zip(prefix[-1],target)]
    if not jac:return r,None,gaps,calibration
    suffix=[None]*(len(factors)+1);suffix[-1]=m.eye(20)
    for k in range(len(factors)-1,-1,-1):suffix[k]=m.mm(factors[k],suffix[k+1])
    dcal=m.vm(prefix[-2],gp.ordinary_derivative(m,E,calibration));cols=[None]*143
    for pos,der,index,ratio in derivatives:
        cols[index]=[v+calibration*ratio*d for v,d in zip(m.vm(m.vm(prefix[pos],der),suffix[pos+1]),dcal)]
    J=[]
    for i in range(20):
        row=[col[i] for col in cols[:108]]
        total=m.mp.fsum(hazards[k]*gaps[k]*cols[108+k][i] for k in range(35))
        row += [-hazards[j]*gaps[j]*cols[108+j][i]+hazards[j]/H*total for j in range(34)]
        J.append(row)
    return r,J,gaps,calibration

def main():
    ap=argparse.ArgumentParser();ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[3]);ap.add_argument("--output",type=Path,required=True);args=ap.parse_args()
    start=time.perf_counter();f=load_fixed();gp=f.load_provider();m=gp.load_provider();m.mp.mp.dps=160
    h=m.load_helper();fa,pin=h.load_source(args.root);states=[h.representative(s,fa) for s in h.SHAPES6];index={s:i for i,s in enumerate(h.SHAPES6)}
    E=h.ordinary_polynomials(states,index,fa);B=full_source_polynomials(states,index,fa,h)
    cp=Path(__file__).with_name("FREE-ARM-GATE-v3.json");raw=cp.read_bytes();receipt=json.loads(raw)
    A=list(map(m.mp.mpf,receipt["saved_final_A_decimal"]));w=list(map(m.mp.mpf,receipt["saved_final_w_decimal"]));theta=list(map(m.mp.mpf,receipt["saved_final_allocation_logits_decimal"]));coin=[m.mp.mpf("0.5")]*36
    t=m.number("1/1024");H=8*(-m.mp.log(m.number("9/10")))+27*(-m.mp.log(1-t))
    # Full arbitrary-coin polynomial agrees with the original rational API at
    # a strict nonfair input before using the candidate.
    x,y,c0=F(1,3),F(3,4),F(2,5)
    for i,state in enumerate(states):
        expected=[F(0)]*20
        for v,p in fa.bigon_law(len(state),x,y,c0,"independent").items():expected[index[h.forest_shape(fa.graft(state,v))]]+=p
        actual=[sum((cc*x**px*y**py*c0**pc for (px,py,pc),cc in p.items()),F(0)) for p in B[i]]
        assert actual==expected
    first,_,_,_=evaluate(f,gp,m,B,E,A,w,coin,theta,H,t,False)
    assert max(abs(v-m.mp.mpf(z)) for v,z in zip(first,receipt["all20_final_residual"]))<m.mp.mpf("1e-145")
    hist=[];stop="predeclared_three_steps_exhausted"
    for step in range(3):
        r,J,gaps,cal=evaluate(f,gp,m,B,E,A,w,coin,theta,H,t)
        before=max(map(abs,r));mat=m.mp.matrix([[J[i][j] for j in range(142)] for i in m.ROWS]);selected=m.mp.matrix([r[i] for i in m.ROWS]);scales=w+A+[min(c-m.mp.mpf("0.25"),m.mp.mpf("0.75")-c) for c in coin]+[m.mp.mpf(1)]*34
        D=m.mp.diag([x*x for x in scales])
        delta=D*mat.T*m.mp.lu_solve(mat*D*mat.T,-selected);alpha=m.mp.mpf(1)
        for j in range(36):
            if delta[j]<0:alpha=min(alpha,m.mp.mpf("0.8")*w[j]/(-delta[j]))
            if delta[36+j]<0:alpha=min(alpha,m.mp.mpf("0.8")*(A[j]-m.mp.sqrt(w[j]*t))/(-delta[36+j]))
            dc=delta[72+j]
            if dc<0:alpha=min(alpha,m.mp.mpf("0.8")*(coin[j]-m.mp.mpf("0.25"))/(-dc))
            elif dc>0:alpha=min(alpha,m.mp.mpf("0.8")*(m.mp.mpf("0.75")-coin[j])/dc)
        maximum=max(abs(delta[j]) for j in range(108,142))
        if maximum:alpha=min(alpha,4/maximum)
        accepted=False;after=None
        for backtrack in range(5):
            nw=[w[j]+alpha*delta[j] for j in range(36)];na=[A[j]+alpha*delta[36+j] for j in range(36)];nc=[coin[j]+alpha*delta[72+j] for j in range(36)];nt=[theta[j]+alpha*delta[108+j] for j in range(34)]
            try:
                rr,_,_,_=evaluate(f,gp,m,B,E,na,nw,nc,nt,H,t,False);after=max(map(abs,rr))
                if after<before:accepted=True;break
            except ValueError:after=None
            alpha/=2
        hist.append({"step":step,"all20_residual_before":[m.mp.nstr(x,150) for x in r],"max_before":m.mp.nstr(before,150),"max_after":m.mp.nstr(after,150) if after else None,"alpha":m.mp.nstr(alpha,150),"accepted":accepted,"backtracks":backtrack,"max_coin_correction":m.mp.nstr(max(abs(delta[72+j]) for j in range(36)),150),"linear_solve_residual":m.mp.nstr(max(map(abs,mat*delta+selected)),150)})
        if not accepted or alpha<m.mp.mpf("1e-6"):stop="strict_source_margin_or_contraction_gate_failed";break
        w,A,coin,theta=nw,na,nc,nt
    low,_,_,_=evaluate(f,gp,m,B,E,A,w,coin,theta,H,t,False)
    saved=[[m.mp.nstr(x,150) for x in v] for v in [A,w,coin,theta]];m.mp.mp.dps=240;t=m.number("1/1024");H=8*(-m.mp.log(m.number("9/10")))+27*(-m.mp.log(1-t));A,w,coin,theta=[list(map(m.mp.mpf,v)) for v in saved]
    high,_,gaps,cal=evaluate(f,gp,m,B,E,A,w,coin,theta,H,t,False)
    result={"status":"BOUNDED_INTERIOR_COIN_COMPLETE_SOURCE_CENTERING_GATE_ONLY","source_sha256":pin,"fixed_provider_sha256":FIXED_SHA,"initial_candidate_sha256":sha256(raw).hexdigest(),"own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),"all20forestrows":True,"strict_coin_interval":"(1/4,3/4)","g_convention":"probability CURRENT ROOT uses x arm; original bits0=x","fixed_t":"1/1024","fixed_total_connector_hazard":True,"controls":142,"max_steps":3,"max_backtracks":5,"history":hist,"stop_reason":stop,"working_digits":160,"replay_digits":240,"source_nonfair_rational_control_all20":True,"saved_final_A":saved[0],"saved_final_w":saved[1],"saved_final_coin":saved[2],"saved_final_allocation_logits":saved[3],"final_calibration":m.mp.nstr(cal,150),"all20_final_residual":[m.mp.nstr(x,150) for x in high],"final_max_residual":m.mp.nstr(max(map(abs,high)),150),"precision_replay_disagreement":m.mp.nstr(max(abs(x-m.mp.mpf(m.mp.nstr(y,150))) for x,y in zip(high,low)),150),"runtime_seconds":time.perf_counter()-start,"not_claimed":["exact common zero","validated radius","all-cap budget","G4 closure"]}
    args.output.write_text(json.dumps(result,indent=2)+"\n");print(json.dumps({"output":str(args.output),"steps":len(hist),"stop_reason":stop,"final_max_residual":result["final_max_residual"],"runtime_seconds":result["runtime_seconds"]}))
if __name__=="__main__":main()
