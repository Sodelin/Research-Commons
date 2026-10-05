"""Symbolic identities only; no source simulation, inverse run or finite-data test."""
import json
import sympy as s
c,T,R,beta,z,a,r,h,u,g,t=s.symbols('c T R beta z a r h u g t', positive=True)
root1=s.exp(-c*T)*R/(R+c);root2=s.exp(-2*c*T)*R/(R+2*c)
rootdet=s.det(s.Matrix([[s.diff(f,x) for x in (T,R)] for f in (root1,root2)]))
assert s.simplify(rootdet-2*c**3*s.exp(-3*c*T)*R/((R+c)**2*(R+2*c)**2))==0
assert s.simplify(root2-root1**2-s.exp(-2*c*T)*R*c**2/((R+2*c)*(R+c)**2))==0
E=s.exp(-(r+z)*(T-a));tail=s.exp(-r*(T-a)-z*T)
M=s.exp(-z*a)*r/(r+z)*(1-E)+tail*R/(R+z)
A=s.exp(-z*a)*(1-E)/(r+z)+tail/(R+z)
V=-s.diff(A,r)
assert s.simplify(s.diff(M,a)+z*r*A)==0
assert s.simplify(s.diff(M,r)-z*V)==0
# These identities remain exact when stage and root rates coincide.
for expr in (s.diff(M,a)+z*r*A,s.diff(M,r)-z*V):assert s.simplify(expr.subs(r,R))==0
D1,D2,D1p,D2p=s.symbols('D1 D2 D1p D2p')
assert s.expand(s.det(s.Matrix([[g*D1p,D1],[g*D2p,D2]]))+g*(D2p*D1-D2*D1p))==0
A1,A2,V1,V2=s.symbols('A1 A2 V1 V2',positive=True)
assert s.simplify(s.det(s.Matrix([[-c*r*A1,c*V1],[-2*c*r*A2,2*c*V2]]))-2*c*c*r*A1*A2*(V1/A1-V2/A2))==0
# Derivative of each post-pulse survival summand has positive exposure.
exposure,C=s.symbols('exposure C',positive=True)
assert s.simplify(s.diff(C*s.exp(-r*exposure),r)+exposure*C*s.exp(-r*exposure))==0
# General pointwise mean-value identity behind the interval contractor.
n=3
xs=s.Matrix(s.symbols('x0:3'));qs=s.Matrix(s.symbols('q0:3'));f=s.Matrix(s.symbols('f0:3'))
Am=s.Matrix(n,n,s.symbols('a0:9'));Y=s.Matrix(n,n,s.symbols('y0:9'))
y=f+Am*(xs-qs)
assert all(s.expand(v)==0 for v in xs-(qs-Y*(f-y)+(s.eye(n)-Y*Am)*(xs-qs)))
# The physical-to-recovery coordinate map is invertible, without a parameter restriction.
x=s.Matrix(s.symbols('h u v rA rB rC rD R g'))
hx,ux,vx,rAx,rBx,rCx,rDx,Rx,gx=x
recovery=s.Matrix([hx+ux+vx,Rx,rCx,hx,gx,hx+ux,rDx,rAx,rBx])
assert abs(recovery.jacobian(x).det())==1
print(json.dumps({'status':'PASS','checks':['root_determinant','root_laplace_variance','AB_onset_derivative','AB_rate_derivative','equal_rate_substitutions','BC_block_determinant','AB_block_determinant','tied_B_exposure_derivative','mean_value_contractor_identity_3D','physical_coordinate_invertibility'],'scope':'Exact symbolic identities supporting the hand proof; no numerical inverse or empirical claim.'},indent=2,sort_keys=True))
