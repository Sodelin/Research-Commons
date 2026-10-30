from fractions import Fraction as F
from pathlib import Path
import json,argparse
import numpy as np
BASE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('engine_root',type=Path);args=ap.parse_args()
from source_bindings import verify
verify(args.engine_root)
# Exact Green identity, with rho=1/9,sigma=4/9 so every transformed coefficient is rational.
rho,sigma=F(1,9),F(4,9);p=[F(1)]
for root in [rho,sigma,rho*sigma]:
 out=[F(0)]*(len(p)+1)
 for i,v in enumerate(p):out[i]-=root*v;out[i+1]+=v
 p=out
p=[v*F(3,2)/sum(p) for v in p];N=len(p)-1
assert all(sum(p[i]*r**i for i in range(N+1))==0 for r in [rho,sigma])
q=[v*F(2,9)**i for i,v in enumerate(p)]
K=lambda i,j:(F(2)**abs(i-j)-F(2)**(-abs(i-j)))/2
f={i:sum(K(i,j)*q[j] for j in range(N+1)) for i in range(-3,N+4)}
assert all(f[i]==0 for i in [-3,-2,-1,N+1,N+2,N+3])
sh,ch=F(3,4),F(5,4)
for i in range(N+1):assert f[i-1]+f[i+1]-2*ch*f[i]==2*sh*q[i]
quad=sum(p[i]*p[j]*rho**i*sigma**j for i in range(N+1) for j in range(i+1,N+1))+sum(v*v*(rho*sigma)**i for i,v in enumerate(p))/2
energy=-(sum((f[i+1]-f[i])**2 for i in range(-1,N+1))+2*(ch-1)*sum(f[i]**2 for i in range(N+1)))/(4*sh)
assert quad==energy<0
# Independent direct path sums on freshly regenerated actual source matrices.
P=10007;z=np.load(BASE/'rebuilt-fullcap-data.npz');old=np.load(args.engine_root/'fullcap-data.npz')
assert all(np.array_equal(z[k],old[k]) for k in old.files)
rc=z['root_counts'];keep=np.flatnonzero(rc>=8);rck=rc[keep];U=z['U'][np.ix_(keep,keep)];T=z['T'][np.ix_(keep,keep)]
# Recover eigenvalues from S*V=V*D, already rechecked by the reconstruction.
D=np.diag((z['W']@z['S']%P)@z['V']%P)[keep];Dp=np.diag(T)
inds={r:np.flatnonzero(rck==r) for r in range(8,13)};aa=inds[12][0];bb=inds[8]
for r in range(9,13):assert not np.any(U[np.ix_(inds[r],inds[r-1])])
M=(U[np.ix_(inds[12],inds[10])]@U[np.ix_(inds[10],inds[8])]%P).reshape(-1)
A=T[aa,bb];B=U[aa,bb]
minor=np.stack([A,B,M])[:,:3];v=minor.tolist();det=(v[0][0]*(v[1][1]*v[2][2]-v[1][2]*v[2][1])-v[0][1]*(v[1][0]*v[2][2]-v[1][2]*v[2][0])+v[0][2]*(v[1][0]*v[2][1]-v[1][1]*v[2][0]))%P
assert det==9400
O=np.zeros_like(U)
for i in range(len(D)):
 for j in range(len(D)):
  if D[i]!=D[j]:O[i,j]=int(T[i,j])*pow(int(D[j]-D[i])%P,-1,P)%P
Uh=(U@O-O@U)%P;U2=U@U%P
j=json.load(open(BASE/'projected-second-check.json'));p=j['effective_first_gap_coefficients_mod'];N=j['N'];h1=-pow(2*N,-1,P)%P
sa,sc,sb=[int(D[inds[r][0]]) for r in [12,10,8]];rh=sa*pow(sc,-1,P)%P;sg=sc*pow(sb,-1,P)%P
R=np.zeros(len(bb),dtype=np.int64)
for i,pi in enumerate(p):
 w=pow(sa,i,P)*pow(sb,N-i,P)%P
 fac=(i*int(Dp[aa])*pow(sa,-1,P)+(N-i)*int(Dp[bb[0]])*pow(sb,-1,P))%P
 R=(R+w*pi*h1%P*Uh[aa,bb]+w*pi*h1%P*fac%P*B+w*pi*pi%P*pow(2,-1,P)%P*U2[aa,bb])%P
 for k in range(i+1,N+1):
  path=(U[aa,:]*np.array([pow(int(dd),k-i,P) for dd in D],dtype=np.int64))@U[:,bb]%P
  R=(R+(pi*p[k]%P)*pow(sa,i,P)%P*pow(sb,N-k,P)%P*path)%P
assert np.array_equal(R,np.array(j['complete_order_u2_residual_mod']))
qq=(sum(p[i]*p[k]*pow(rh,i,P)*pow(sg,k,P) for i in range(N+1) for k in range(i+1,N+1))+pow(2,-1,P)*sum(pi*pi*pow(rh*sg%P,i,P) for i,pi in enumerate(p)))%P
rem=(R-pow(sb,N,P)*qq*M)%P;pivot=next(k for k,x in enumerate(B) if x);coeff=int(rem[pivot])*pow(int(B[pivot]),-1,P)%P
assert np.array_equal(rem,coeff*B%P)
out={'status':'PASS','rebuilt_source_arrays_equal_saved':True,'source_shape_minor_mod':det,'direct_path_sum_matches_full_product_residual':True,'residual_modulo_U_equals_ordered_coefficient_M':True,'green_rational_quadratic':str(quad),'green_exact_energy':str(energy),'scope':'Independent exact algebra and rebuilt actual modular source controls; no sign inferred modulo prime, no master closure.'}
(BASE/'review-check-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
