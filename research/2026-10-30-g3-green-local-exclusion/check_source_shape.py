import sys,json,argparse
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('engine_root',type=Path);ap.add_argument('--prior-packet',type=Path,default=Path(__file__).resolve().parent);args=ap.parse_args()
from source_bindings import verify
verify(args.engine_root)
import hashlib
m=json.loads(Path(__file__).with_name('SOURCE-BINDINGS.json').read_text())['prior_checked_tangent']
assert hashlib.sha256((args.prior_packet/m['path']).read_bytes()).hexdigest()==m['sha256']
sys.path.insert(0,str(args.engine_root));from forest_modular import *
z=np.load(args.engine_root/'fullcap-data.npz');rc=z['root_counts'];T,U=z['T'],z['U'];D=np.diag(mm(mm(z['W'],z['S']),z['V']))
inds={r:np.flatnonzero(rc==r) for r in [12,11,10,9,8]};a,c,b=12,10,8
for r in range(2,13):assert np.count_nonzero(U[np.ix_(np.flatnonzero(rc==r),np.flatnonzero(rc==r-1))])==0
A=T[np.ix_(inds[a],inds[b])].reshape(-1);B=U[np.ix_(inds[a],inds[b])].reshape(-1)
M=mm(U[np.ix_(inds[a],inds[c])],U[np.ix_(inds[c],inds[b])]).reshape(-1)
minor=np.stack([A,B,M])[:,[0,1,2]].tolist();(aa,bb,cc),(dd,ee,ff),(gg,hh,ii)=minor;det=(aa*(ee*ii-ff*hh)-bb*(dd*ii-ff*gg)+cc*(dd*hh-ee*gg))%P;assert det!=0
old=json.loads((args.prior_packet/'projected-second-check.json').read_text());p=old['effective_first_gap_coefficients_mod'];N=old['N'];sa,sc,sb=[int(D[inds[r][0]]) for r in [a,c,b]];rho=sa*pow(sc,-1,P)%P;sigma=sc*pow(sb,-1,P)%P
assert all(sum(v*pow(z,j,P) for j,v in enumerate(p))%P==0 for z in [rho,sigma,sa*pow(sb,-1,P)%P])
Q=sum(p[i]*p[j]*pow(rho,i,P)*pow(sigma,j,P) for i in range(N+1) for j in range(i+1,N+1))
Q+=pow(2,-1,P)*sum(v*v*pow(rho*sigma%P,i,P) for i,v in enumerate(p));Q%=P
coef=pow(sb,N,P)*Q%P;R=np.array(old['complete_order_u2_residual_mod'],dtype=np.int64);rem=(R-coef*M)%P
assert span_rank([B,rem])==1
out={'status':'PASS source binding for all-N proof','prime':P,'reference_t_rational':[999,1000],'root_path':[12,10,8],'all_adjacent_U_bands_zero_mod':True,'T_U_M_full_rows_mod':[A.tolist(),B.tolist(),M.tolist()],'minor_columns':[0,1,2],'minor_matrix_mod':minor,'minor_determinant_mod':det,'prior_tangent_factorization_check':{'rho_mod':rho,'sigma_mod':sigma,'ordered_quadratic_mod':Q,'coefficient_sb_powerN_times_Q_mod':coef,'residual_minus_coefficient_M_in_U_span':True},'scope':'Actual source shape witness plus replay of exact general factorization on prior tangent; no new tangent sample or sign inferred from residues.'}
Path(__file__).with_name('SOURCE-SHAPE-MINOR.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
