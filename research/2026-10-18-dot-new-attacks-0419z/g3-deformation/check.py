import sympy as s, json
from pathlib import Path
L=[1,3,6,10,15,21,28]; p=s.Rational(1,100); q=s.Rational(1,2)
rows=[]
for l in L:
 f=1-p+p*q**l; D=1-q**l
 rows.append([l,D/f,-p*l*q**(l-1)/f,D**2/f**2,-l*q**(l-1)/f**2,-p*l*(l-1)*q**(l-2)/f+p**2*l**2*q**(2*l-2)/f**2])
# Independently differentiate the log factor before substituting the rational node.
P,Q=s.symbols('P Q', positive=True)
for l,row in zip(L,rows):
 h=-s.log(1-P+P*Q**l)
 derivatives=[s.diff(h,P),s.diff(h,Q),s.diff(h,P,2),s.diff(h,P,Q),s.diff(h,Q,2)]
 assert all(s.simplify(d.subs({P:p,Q:q})-v)==0 for d,v in zip(derivatives,row[1:]))
A=s.Matrix(rows); assert A.rank()==6
u=s.Rational(1,30); M=A.row_join(s.Matrix([1-u**l for l in L])); assert M.det()!=0
c=(M.T).inv()*s.Matrix([0,0,0,1,0,1,-1]); assert M.T*c==s.Matrix([0,0,0,1,0,1,-1])
# Two freely variable literal heads: derivative rank3, nullity2.
J=s.Matrix.hstack(A[:,0],A[:,1],A[:,2],A[:,1],A[:,2]);assert J.rank()==3
out={'p':str(p),'q':str(q),'rare_append_survival':str(u),'rates':L,'rank_six_jet':A.rank(),'normal':[str(x) for x in c],'normal_pairings':[str(x) for x in M.T*c],'N2_derivative_rank':J.rank(),'N2_derivative_nullity':len(J.nullspace()),'status':'PASS exact rational identities; analytic isolation is a hand argument'}
Path(__file__).with_name('RESULT.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps({k:v for k,v in out.items() if k!='normal'},indent=2))
