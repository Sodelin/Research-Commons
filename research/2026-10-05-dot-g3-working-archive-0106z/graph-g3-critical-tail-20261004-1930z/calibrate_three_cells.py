"""Bounded numerical negative-control search only; no exact or all-cap claim."""
import json, math
import numpy as np
from scipy.optimize import least_squares
from pathlib import Path

def B(x,y):
 g=.5
 b=[sum(math.comb(k,r)*g**k*x**(r*(r-1)//2)*y**((k-r)*(k-r-1)//2) for r in range(k+1)) for k in (2,3,4)]
 A=(1-x)/2; V=(1-y)/2
 C=(A**3+V**3)/3-(A-V)**2/2
 return np.array(b+[C,0.])
def E(z):return np.array([z,z**3,z**6,0.,0.])
def mul(K,L):
 return np.array([K[0]*L[0],K[1]*L[1],K[2]*L[2],L[0]*K[3]+K[2]*L[3],K[4]+(1-L[0])*K[3]+K[2]*L[4]])
def body(v):
 K=B(*v[:2]);K=mul(K,E(v[6]));K=mul(K,B(*v[2:4]));K=mul(K,E(v[7]));return mul(K,B(*v[4:6]))
def fun(v):
 b2,b3,b4,C,H=body(v)
 return np.array([math.log(b3)-3*math.log(b2),math.log(b4)-6*math.log(b2),C*100,H*100])
rng=np.random.default_rng(90817);out=[]
for i in range(10):
 v=rng.uniform(.2,.85,8)
 result=least_squares(fun,v,bounds=(np.full(8,.08),np.full(8,.96)),max_nfev=1600,ftol=1e-13,xtol=1e-13,gtol=1e-13)
 row={'seed':i,'parameters':result.x.tolist(),'residual':fun(result.x).tolist(),'norm':float(np.linalg.norm(fun(result.x))),'nfev':result.nfev,'kernel':body(result.x).tolist(),'jacobian_rank_numeric':int(np.linalg.matrix_rank(result.jac,tol=1e-9))}
 out.append(row)
 if row['norm']<1e-10 and np.min(result.x-.08)>.001 and np.min(.96-result.x)>.001:break
p=Path(__file__).with_name('THREE-CELL-NUMERICAL-CALIBRATION.json');p.write_text(json.dumps({'status':'NUMERICAL_CANDIDATES_ONLY_NOT_A_PROOF','scope':'one fixed cap-four exact quotient, three independent cells, g=1/2, all physical survivals constrained to [.08,.96]','results':out},indent=2)+'\n')
print(json.dumps(min(out,key=lambda z:z['norm']),indent=2))
