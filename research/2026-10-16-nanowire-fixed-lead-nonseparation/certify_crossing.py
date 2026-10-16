"""Own finite-chain certificate generator/checker. Floats propose; rational bounds certify.
No claim that this declares Taylor et al.'s undisclosed lead implementation.
"""
import json, math, hashlib
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.linalg import eig, svd
N=58; n=2*N; t0=F('25.08215'); lam=F('2.5'); B=F(2); Delta=F('.2')
wt=F('0.00005'); wx=F('0.0001'); S=2**80

def matrix(t,a):
 A=np.zeros((n,n),dtype=object)
 for k in range(N):
  A[2*k:2*k+2,2*k:2*k+2]=[[a,-B+Delta],[B+Delta,-a]]
  if k<N-1:
   A[2*k:2*k+2,2*k+2:2*k+4]=[[-t,lam],[lam,t]]
   A[2*k+2:2*k+4,2*k:2*k+2]=[[-t,-lam],[-lam,t]]
 return A
D=np.diag(np.tile([1,-1],N)).astype(object)
C=np.array(matrix(t0,F(0)),float)
vals=eig(-np.array(D,float)@C,left=False,right=False)
roots=[v.real for v in vals if abs(v.imag)<1e-8 and .6<2*float(t0)-v.real<1]
a0=F(f'{min(roots,key=lambda a:abs(2*float(t0)-a-.785)):.12f}')
A=matrix(t0,a0); Af=np.array(A,float);U,ss,V=svd(Af)
i=int(np.argmax(abs(U[:,-1])));j=int(np.argmax(abs(V[-1])));
rows=[k for k in range(n) if k!=i]; cols=[k for k in range(n) if k!=j]
M=A[np.ix_(rows,cols)]; inv=np.linalg.inv(np.array(M,float))
Ri=np.array([[round(F(float(x))*S) for x in row] for row in inv],dtype=object)
# Persist the proposal. All bounds below use this integer R, not numerical svd/eig.
cert={'N':N,'t_center':str(t0),'t_halfwidth':str(wt),'x_center':str(a0),'x_halfwidth':str(wx),'lambda':str(lam),'B':str(B),'Delta':str(Delta),'deleted_row':i,'deleted_column':j,'inverse_denominator':str(S),'inverse_numerators':[[str(x) for x in row] for row in Ri]}
p=Path(__file__).with_name('CROSSING-CERTIFICATE.json');p.write_text(json.dumps(cert,separators=(',',':'))+'\n')
R=np.array([[F(x,S) for x in row] for row in Ri],dtype=object)
# Rational residual and norm bounds.
norm12=lambda Z:max(max(sum(abs(F(x)) for x in row) for row in Z),max(sum(abs(F(x)) for x in col) for col in Z.T))
Eres=np.eye(n-1,dtype=object)-R@M
e=norm12(Eres); K=norm12(R); rho=wx+4*wt
assert e+K*rho<1
Ki=K/(1-e-K*rho); Ki0=K/(1-e)
Q=10**12
def lo_sqrt(v):
 v=F(v);return F(math.isqrt(v.numerator*Q*Q//v.denominator),Q)
def hi_sqrt(v): return lo_sqrt(v)+F(1,Q)
def dot(v,w):return sum((F(x)*F(y) for x,y in zip(v,w)),F(0))
def nup(v):return hi_sqrt(dot(v,v))
def vres(v):return nup(v)
q=np.zeros(n,dtype=object);q[j]=F(1);q[cols]=-R@A[rows,j]
pv=np.zeros(n,dtype=object);pv[i]=F(1);pv[rows]=-R.T@A[i,cols]
qn=nup(q);pn=nup(pv)
rq=vres((A@q)[rows]);rp=vres((A.T@pv)[cols])
eq=Ki*(rq+rho*qn);ep=Ki*(rp+rho*pn)
eq0=Ki0*rq;ep0=Ki0*rp
# F(x,t)=A_ij-r M^-1 c. Its derivatives are p^T (dA) q, p_i=q_j=1.
E=matrix(t0+1,a0+2)-A
fx=dot(pv,D@q); ft=dot(pv,E@q)
ferr=ep*qn+eq*pn+ep*eq
fxlo=fx-ferr;fxhi=fx+ferr
ftabs=abs(ft)+4*ferr
f0=dot(A[i,:],q); f0err=nup(A[i,cols])*eq0
assert fxlo>0
assert fxlo*wx>ftabs*wt+abs(f0)+f0err
# Endpoint chirality polarization. The normalization cancels in this ratio.
pL=dot(pv[:2],pv[:2]);pR=dot(pv[-2:],pv[-2:])
errL=2*nup(pv[:2])*ep+ep*ep;errR=2*nup(pv[-2:])*ep+ep*ep
contrast_lo=(pL-pR-errL-errR)/(pL+pR+errL+errR)
contrast_hi=(pL-pR+errL+errR)/(pL+pR-errL-errR)
assert pL+pR>errL+errR
assert contrast_lo>F(19,50) # square > .1444
# Crossing velocity in normalized chiral vectors.
slope_lo=fxlo/((pn+ep)*(qn+eq))
assert slope_lo>F(9,10)
# Normalized total boundary mass and g bound, kappa=1.
assert lo_sqrt(dot(pv,pv))>ep
bmass_hi=(pL+pR+errL+errR)/(lo_sqrt(dot(pv,pv))-ep)**2
rhohop_hi=(t0+wt)**2+lam**2
g_hi=rhohop_hi*bmass_hi
assert g_hi<6
bmass_lo=(pL+pR-errL-errR)/(pn+ep)**2
g_lo=((t0-wt)**2+lam**2)*bmass_lo
assert g_lo>F(9,2)
cminus=F(1,100)
zmax=(cminus/g_lo)**2
negative=(zmax-contrast_lo**2)/(zmax+1)
assert negative<F(-15,100)
# For c=100: positive limiting TV >= (c^2*slope_lo^2-g_hi^2)/(c^2*slope_lo^2+g_hi^2).
c=F(100);positive=(c*c*slope_lo*slope_lo-g_hi*g_hi)/(c*c*slope_lo*slope_lo+g_hi*g_hi)
assert positive>F(99,100)
fields={'e':e,'K':K,'rho':rho,'inverse_bound':Ki,'p_error':ep,'q_error':eq,'F_x_lower':fxlo,'F_x_upper':fxhi,'F_t_abs_upper':ftabs,'center_F_abs_bound':abs(f0)+f0err,'contrast_lower':contrast_lo,'contrast_upper':contrast_hi,'negative_c_zero_limit_upper':-contrast_lo**2,'negative_c_001_limit_upper':negative,'normalized_slope_lower':slope_lo,'g_upper':g_hi,'g_lower':g_lo,'positive_limit_lower':positive}
result={'status':'exact-rational inequalities passed; hand asymptotic transfer not automated','certificate_sha256':hashlib.sha256(Path(__file__).with_name('CROSSING-CERTIFICATE.json').read_bytes()).hexdigest(),'parameters':{k:v for k,v in cert.items() if k!='inverse_numerators'},'bounds':{k:{'exact':str(v),'decimal':float(v)} for k,v in fields.items()}}
Path(__file__).with_name('CROSSING-CERTIFICATE-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
for k,v in fields.items():print(k,float(v))
print('CERTIFICATE',result['certificate_sha256']);print('ALL RATIONAL CHECKS PASS')
