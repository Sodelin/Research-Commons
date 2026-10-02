"""Generate exact constant evaluation/column transforms for Lean replay.
No Lean proof is claimed by this generator; every identity must compile.
"""
import sympy as S,json,time,resource,pathlib
resource.setrlimit(resource.RLIMIT_CPU,(60,60));resource.setrlimit(resource.RLIMIT_AS,(900*1024**2,900*1024**2))
t0=time.monotonic();p=S.symbols('p');ls=[1,3,6,10,15,21];out=[]
for z in [3,5]:
 f=[S.Poly(1-p+p*z**l,p,domain=S.QQ) for l in ls]
 Ps=[];Qs=[]
 for k in range(5):
  b=[S.Rational(int(i==k)) for i in range(5)]+[-S.Rational(ls[k],21)]
  P=S.Poly(0,p,domain=S.QQ);Q0=P
  for i,l in enumerate(ls):
   term=S.Poly(1,p,domain=S.QQ)
   for j in range(6):
    if j!=i:term*=f[j]
   P+=term.mul_ground(b[i]*(1-z**l));Q0+=term.mul_ground(b[i]*l*z**(l-1))
  Q=Q0.exquo(S.Poly(1-p,p,domain=S.QQ));assert P.degree()<=5 and Q.degree()<=4
  Ps.append(P);Qs.append(Q)
 Sm=[]
 for P,Q in zip(Ps,Qs):
  Sm.append(S.Matrix(9,9,lambda i,j:Q.nth(i-j) if j<5 and 0<=i-j<=4 else (P.nth(i-(j-5)) if j>=5 and 0<=i-(j-5)<=5 else 0)))
 rho=[-S.Rational(1,z**l-1) for l in ls]
 KP=[(1-z**ls[i])*S.prod(f[j].eval(rho[i]) for j in range(6) if j!=i) for i in range(6)]
 T=S.Matrix(9,9,lambda i,j:rho[i]**j/KP[i] if i<6 else S.Rational(int(j==i)))
 A=S.Matrix(6,9,lambda i,j:-S.Rational(ls[i],z)*rho[i]**j if j<5 else rho[i]**(j-5))
 for k,M in enumerate(Sm):
  N=T*M
  for i in range(6):
   b=S.Rational(int(i==k)) if i<5 else -S.Rational(ls[k],21)
   assert N[i,:]==b*A[i,:]
 piv=list(A.rref()[1]);assert len(piv)==6;free=[j for j in range(9) if j not in piv]
 AJ=A[:,piv];AK=A[:,free];AJinv=AJ.inv()
 Perm=S.Matrix(9,9,lambda i,j:S.Rational(int(i==(piv+free)[j])))
 Rblock=S.eye(9);Rblock[:6,:6]=AJinv;Rblock[:6,6:9]=-AJinv*AK
 R=Perm*Rblock
 assert A*R==S.eye(6).row_join(S.zeros(6,3))
 Ri=R.inv();Ti=T.inv();assert R*Ri==S.eye(9) and T*Ti==S.eye(9)
 Ns=[T*M*R for M in Sm]
 for k,N in enumerate(Ns):
  for i in range(6):
   bi=S.Rational(int(i==k)) if i<5 else -S.Rational(ls[k],21)
   for j in range(9):assert N[i,j]==(bi if i==j else 0)
 def mat(M):return [[str(x) for x in row] for row in M.tolist()]
 rec={'q':z,'lambda':ls,'P_coefficients_ascending_by_free_weight':[[str(P.nth(i)) for i in range(6)] for P in Ps],
 'Q_coefficients_ascending_by_free_weight':[[str(Q.nth(i)) for i in range(5)] for Q in Qs],
 'T':mat(T),'T_inverse':mat(Ti),'R':mat(R),'R_inverse':mat(Ri),
 'reduced_bottom_rows_by_free_weight':[mat(N[6:9,:]) for N in Ns],
 'residual_C_by_free_weight':[mat(N[6:9,6:9]) for N in Ns],
 'T_determinant':str(T.det()),'R_determinant':str(R.det()),'pivot_columns':piv,'seconds_from_start':time.monotonic()-t0}
 out.append(rec)
 print(json.dumps({'q':z,'status':'exact transform identities checked; Lean replay pending','seconds':time.monotonic()-t0}),flush=True)
pathlib.Path('/workspace/shared/lean-formalization/g3-sylvester-transform-certificate.json').write_text(json.dumps({'records':out,'seconds':time.monotonic()-t0},indent=2)+'\n')
