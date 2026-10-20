"""Bounded floating evaluation of explicit proof bounds, not entropy simulation.
No tensor matrices or external data. Mathematical proof is in the adjacent note.
"""
import math
print('beta=2, k=2; natural-log information units; finite-grid bound evaluations')
for N in [64,128,256,512,1024]:
    n=math.floor(math.exp(N/4))
    L=math.floor(math.exp(N/16))
    r=N*(N+1)//2
    M=3*N+9*N*(N-1)//2
    logq=-(2-math.log(2))*N
    # h2(q) <= q*(1-log q). Thus chi_n <= n*q*(1-log q+N log2).
    log_chi_upper=math.log(n)+logq+math.log(1-logq+N*math.log(2))
    chi_upper=math.exp(log_chi_upper) if log_chi_upper>-745 else 0.0
    loge=min(0.0,math.log(2*r)-n/(8*(L-1)**2))
    e=math.exp(loge) if loge>-745 else 0.0
    assert e<0.5
    # h2(e) <= e*(1-log e), safely evaluated before underflow.
    h_e_upper=math.exp(loge+math.log(1-loge)) if loge+math.log(1-loge)>-745 else 0.0
    residual_lower=(1-e)*r*math.log(L)-h_e_upper-chi_upper
    assert residual_lower>0
    assert log_chi_upper<0
    print(f'N={N:4d}, log(chi_n upper)={log_chi_upper:.6f}, log(error upper)={loge:.6g}, residual lower/M={residual_lower/M:.6f}')
print('PASS: five finite bound evaluations. Floating arithmetic is diagnostic, not a certificate.')
