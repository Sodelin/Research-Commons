"""Own exact integer residual certificate; NumPy only proposes an inverse."""
from fractions import Fraction as F
from math import isqrt
import numpy as np
import json, hashlib, pathlib, time, sys
if sys.flags.optimize: raise RuntimeError("Run without -O; exact guards are required")
ROOT=pathlib.Path(__file__).resolve().parent
n=240; den=25000000000000; scale=1<<48
T=[[F(-501643,20000),0,F(-5,2),0],[0,F(501643,20000),0,F(5,2)],[F(5,2),0,F(-501643,20000),0],[0,F(-5,2),0,F(501643,20000)]]
H=[[F(0) for _ in range(n)] for _ in range(n)]
for site in range(60):
 a=F(1000) if site in (0,59) else F(1234321162378001,den)
 A=[[a,F(1,5),2,0],[F(1,5),-a,0,2],[2,0,a,F(1,5)],[0,2,F(1,5),-a]]
 for i in range(4):
  for j in range(4):
   H[4*site+i][4*site+j]=F(A[i][j])
   if site<59:
    H[4*site+i][4*(site+1)+j]=F(T[i][j]); H[4*(site+1)+j][4*site+i]=F(T[i][j])
assert all(H[i][j]==H[j][i] for i in range(n) for j in range(n))
# Exact physical PHS involution J= sigma_y tensor tau_y, a signed permutation.
perm=[3,2,1,0]; sign=[-1,1,1,-1]
assert all(sign[i%4]*sign[j%4]*H[4*(i//4)+perm[i%4]][4*(j//4)+perm[j%4]] == -H[i][j] for i in range(n) for j in range(n))
prior_path=ROOT/'PRIOR-CONDUCTANCE-RESULT.json'
prior=json.loads(prior_path.read_text())
assert prior['status']=='PASS' and prior['electron_indices']==[0,2] and prior['hole_indices']==[1,3]
assert F(prior['values']['plus']['g_LL']['upper']) < F(1,250)
assert F(prior['values']['plus']['g_LL']['lower']) > 0
rows=[]
for i in range(n):
 row=[]
 for j in range(n):
  re=-H[i][j]*den; assert re.denominator==1
  im=den if i==j and (i<4 or i>=236) else 0
  if re or im: row.append((j,int(re),im))
 rows.append(row)
K=np.zeros((n,n),dtype=complex)
for i,row in enumerate(rows):
 for j,a,b in row: K[i,j]=complex(a/den,b/den)
t0=time.time(); Z=np.linalg.inv(K)
# Floating-point output is untrusted; every following acceptance is integer/rational.
zr=[[int(round(float(Z[i,j].real)*scale)) for j in range(n)] for i in range(n)]
zi=[[int(round(float(Z[i,j].imag)*scale)) for j in range(n)] for i in range(n)]
rsq=0; zsq=sum(zr[i][j]**2+zi[i][j]**2 for i in range(n) for j in range(n))
for i,row in enumerate(rows):
 for j in range(n):
  a=sum(x*zr[k][j]-y*zi[k][j] for k,x,y in row)-(den*scale if i==j else 0)
  b=sum(x*zi[k][j]+y*zr[k][j] for k,x,y in row)
  rsq+=a*a+b*b
def ceil_sqrt(x):
 y=isqrt(x); return y+(y*y<x)
r=ceil_sqrt(rsq); z=ceil_sqrt(zsq)
assert r*r>=rsq and z*z>=zsq and (r-1)**2<rsq and (z-1)**2<zsq
assert r<den*scale
rho=F(den*scale-r,den*z)
# Honest fixed-temperature budget, using rational elementary bounds only.
W=rho/2; assert W<1
L=F(4)+32/rho**2 # beta_W>=1/2; N=2, d=rho/2.
theta=rho**2/10000
p_upper=2*theta/W # exp(W/theta)>=W/theta, sufficient upper bound
assert p_upper<1
# Prior exact certificate: f(0)<.004. Global local conductance <=4.
warm_upper=F(1,250)+2*L*theta+4*p_upper
eta=F(1,1000)
y_upper=warm_upper+eta # every deterministic measurement error <=eta
U=(y_upper+eta+2*L*theta)/(1-p_upper) # Delta_H=0, same H
assert U<1
kb_mev=F(1380649,10**29)/F(1602176634,10**31) # J/K divided by J/meV
assert F(8,100)<kb_mev<F(9,100)
files={'inverse_gaussian_integer.json':{'denominator':scale,'real':zr,'imag':zi},'scaled_K_rows.json':{'denominator':den,'rows':rows}}
for name,data in files.items(): (ROOT/name).write_text(json.dumps(data,separators=(',',':'))+'\n')
result={'status':'PASS','dimension':n,'source_model_commit':'b6b1f91d84e58506b9028dec1ff0c59e05317224','profile':'positive','B_meV':'2','rho_lower':str(rho),'rho_decimal_display':float(rho),'residual_frobenius_upper':str(F(r,den*scale)),'inverse_frobenius_upper':str(F(z,scale)),'residual_squared_integer':str(rsq),'inverse_squared_integer':str(zsq),'residual_ceil_sqrt':str(r),'inverse_ceil_sqrt':str(z),'W_dimensionless':str(W),'L_upper':str(L),'theta_dimensionless':str(theta),'temperature_K':str(theta/kb_mev),'temperature_K_display':float(theta/kb_mev),'measurement_eta_e2_over_h':str(eta),'warm_conductance_upper':str(warm_upper),'Q_lower':str(1-U),'Q_lower_display':float(1-U),'Hamiltonian_drift':'0, identical frozen H','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'prior_conductance_sha256':hashlib.sha256(prior_path.read_bytes()).hexdigest(),'artifact_sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in files}}
(ROOT/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','rho_decimal_display','temperature_K_display','Q_lower_display']},indent=2))
print('Exact residual epsilon display:',float(F(r,den*scale)))
print('Elapsed seconds:',time.time()-t0)
