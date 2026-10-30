import argparse,sys,json
from fractions import Fraction
from math import comb
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('engine_root',type=Path);args=ap.parse_args();sys.path.insert(0,str(args.engine_root))
from source_bindings import verify
verify(args.engine_root)
from forest_modular import *
z=np.load(args.engine_root/'fullcap-data.npz');rc=z['root_counts'];keep=np.flatnonzero(rc>=8);T=z['T'][np.ix_(keep,keep)];U=z['U'][np.ix_(keep,keep)];Dall=np.diag(mm(mm(z['W'],z['S']),z['V']));D=Dall[keep];Dp=np.diag(T)
t=Fraction(999,1000);sr={}
for r in range(1,13):
 L=r*(r-1)//2;sr[r]=sum(Fraction(comb(r,k),2**r)*t**(3*L+lam(k)+lam(r-k))*(2-t)**(L-lam(k)-lam(r-k)) for k in range(r+1))
rats=sorted({sr[a]/sr[b] for a in range(2,13) for b in range(1,a)})
assert all(all(int(v)==(sr[r].numerator*pow(sr[r].denominator,-1,P)%P) for v in Dall[np.flatnonzero(rc==r)]) for r in range(1,13))
rhos=[r.numerator*pow(r.denominator,-1,P)%P for r in rats];N=len(rhos);assert N==66 and len(set(rhos))==N and 1 not in rhos
# Rationally defined polynomial p(z)=(3/2) product(z-rho)/product(1-rho).
p=[1]
for rho in rhos:
 out=[0]*(len(p)+1)
 for j,c in enumerate(p):out[j]=(out[j]-rho*c)%P;out[j+1]=(out[j+1]+c)%P
 p=out
scale=3*pow(2,-1,P)*pow(sum(p)%P,-1,P)%P;p=[c*scale%P for c in p]
assert sum(p)%P==3*pow(2,-1,P)%P
assert all(sum(c*pow(rho,j,P) for j,c in enumerate(p))%P==0 for rho in rhos)
O=np.zeros_like(U)
for i in range(len(D)):
 for j in range(len(D)):
  if D[i]!=D[j]:O[i,j]=T[i,j]*pow(int(D[j]-D[i])%P,-1,P)%P
Uh=(mm(U,O)-mm(O,U))%P;U2=mm(U,U);h1=-pow(2*N,-1,P)%P
K0=np.eye(len(D),dtype=np.int64);K1=np.zeros_like(U);K2=np.zeros_like(U)
for j in range(N+1):
 G1=p[j]*U%P;G2=(p[j]*h1*Uh+p[j]*p[j]*pow(2,-1,P)*U2)%P
 K2=(K2+mm(K1,G1)+mm(K0,G2))%P;K1=(K1+mm(K0,G1))%P
 if j<N:
  K2=(K2*D[None,:]+K1*(h1*Dp%P)[None,:])%P
  K1=(K1*D[None,:]+K0*(h1*Dp%P)[None,:])%P
  K0=K0*D[None,:]%P
assert np.count_nonzero(K1-np.diag(np.diag(K1)))==0
loc_rc=rc[keep];cols=np.flatnonzero(loc_rc==8);row=0
A=T[row,cols];B=U[row,cols];R=K2[row,cols]
rank=span_rank([A,B]);rank2=span_rank([A,B,R])
M=np.stack([A,B,R])%P;G=M.copy();piv=[]
for i in range(3):
 j=int(np.flatnonzero(G[i])[0]);piv.append(j);G[i]=G[i]*pow(int(G[i,j]),-1,P)%P
 for k in range(i+1,3):G[k]=(G[k]-G[k,j]*G[i])%P
minor=M[:,piv].tolist()
a,b,c=minor[0];d,e,f=minor[1];g,h,i=minor[2]
det=(a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g))%P
assert det!=0
out={'selected_residual_minor_columns':piv,'residual_minor_matrix_mod':minor,'residual_minor_det_mod':det,'status':'PASS computed complete projected second residual','prime':P,'cap':12,'reference_t_rational':[999,1000],'N':N,'retained_root_levels':[12,11,10,9,8],'retained_dimension':len(D),'total_ratios':N,'all_ratio_moments_zero':True,'effective_first_gap_coefficients_mod':p,'actual_gap_formula':'r_j=p_j-(1/2)*1_{j=d}; any junction d; sum r=1','reference_h_first_coefficient_mod':h1,'first_full_commutator_offdiagonal':'PASS on all imposed root ratios','block':[12,8],'reference_tangent_rows_mod':[A.tolist(),B.tolist()],'complete_order_u2_residual_mod':R.tolist(),'base_shape_rank':rank,'rank_with_residual':rank2,'interpretation':'This is one actually clock-compatible rationally defined first tangent; second-order corrections project into the reference T/U shape span. Rank increase rejects only this chosen first tangent. No claim against all first gap solutions, larger N, or integrated branches.'}
Path(__file__).with_name('projected-second-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['effective_first_gap_coefficients_mod','reference_tangent_rows_mod','complete_order_u2_residual_mod']},indent=2))
