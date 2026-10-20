"""Finite evaluations of the proof's scalar bounds, not a tensor-state simulation.
Standard-library floating arithmetic, not interval certification or formal proof.
"""
import math
BETA=2.
def logadd(a,b):
 m=max(a,b);return m+math.log(math.exp(a-m)+math.exp(b-m))
def exp_safe(a):return math.exp(a) if a>-745 else 0.
def g(x):return math.log1p(x)+x*math.log1p(1/x)
print('beta=2, k=2, n=N^20; all information uses natural logarithms')
for N in [8,16,64,256,4096,2**20,2**32]:
 r=N*(N-1)//2;M=3*N+9*r;Delta=2*(N-1)
 ln=20*math.log(N);lr=math.log(r);ld=math.log(Delta)
 lR=lr+ld-ln/2;R=math.exp(lR)
 lQ=logadd(math.log(N+1)-2*N,N*math.log(2)-4*(N-1))
 c=(1-exp_safe(-2*Delta))/(1+exp_safe(lQ))
 taylor=math.exp(math.log(3*BETA**2)+2*lr+2*ld-ln/2)
 assert c>=.75 and taylor<=.25 and R<=N/4
 leta=math.log(256)+4*lr-ln
 # The exact integer D=2^N-r-1 need not be materialized: upper-bound it by 2^N.
 log_one_D_over_eta=N*math.log(2)-leta
 if log_one_D_over_eta<50:log_one_D_over_eta=math.log1p(math.exp(log_one_D_over_eta))
 extra=exp_safe(leta)*(1+log_one_D_over_eta)
 leps=4*R+lQ
 lthermal=2*ln+math.log(N*math.log(2))+leps
 ltrace=ln+leps
 thermal=exp_safe(lthermal)+exp_safe(ltrace)*(1-ltrace)
 logs=.5*(math.log(4)+math.log(M)-math.log(BETA)-ld)
 packing_per_r=.5*lr-logs-.5*math.log(2*math.pi*math.e)
 h_lower=(r*(packing_per_r-g(16))-extra-thermal)/M if ltrace<math.log(.5) else None
 print(f'N={N:>10}, Taylor_error={taylor:.4g}, eta={exp_safe(leta):.4g}, log(n^2 N ln2 eps)={lthermal:.5g}, H_lower/M={format(h_lower, '.6f') if h_lower is not None else 'not applied: n*eps >= 1/2'}')
print('PASS: seven finite scalar-bound evaluations; positive asymptotic obstruction visible for large N.')
print('Entropy continuity is applied only when n*epsilon < 1/2. Negative valid lower bounds do not assert negative entropy.')
