import sympy as s
I=s.eye(2); X=s.Matrix([[0,1],[1,0]]);Y=s.Matrix([[0,-s.I],[s.I,0]]);Z=s.diag(1,-1)
k=s.kronecker_product
P=(k(Z,I)+k(X,X))/s.sqrt(2);Q=(k(Z,I)-k(X,X))/s.sqrt(2);T=k(Y,X)
basis=[s.eye(4),P,Q,T]
r0,e,r,f,d,t=s.symbols('r0 e r f d t',real=True)
expected=[s.Matrix([[0,0,0,0],[-8*r*t,-8*r,0,0],[0,0,-4*(r+r0),4*d],[0,0,-4*d,-4*(r+r0)]]),s.Matrix([[0,0,0,0],[-4*r*t,-4*r,4*r0,0],[4*r*t,4*r,-4*r0,0],[4*(e-f),-4*d,-4*d,-4*(r+r0)]])]
for site in [0,1]:
 for j,B in enumerate(basis):
  total=s.zeros(4)
  for a in [X,Y,Z]:
   A=k(a,I) if site==0 else k(I,a)
   Ac=(A+P*A*P)/2;Aa=(A-P*A*P)/2
   F=(r0+s.I*e)*Ac+(r+s.I*f)*Aa-s.I*(d-s.I*t*r)*P*Aa
   total+=F*B*A-A*F*B+A*B*F.conjugate().T-B*F.conjugate().T*A
  target=sum((expected[site][i,j]*basis[i] for i in range(4)),s.zeros(4))
  assert (total-target).applyfunc(s.simplify)==s.zeros(4)
print('PASS independent exact reconstruction: both grouped three-axis maps on all four basis elements; SymPy',s.__version__)
