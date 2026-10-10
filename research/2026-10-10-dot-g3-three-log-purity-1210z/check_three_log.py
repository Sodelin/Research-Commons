from pathlib import Path
import json
import sympy as s
R=Path(__file__).resolve().parent
r,x,y=s.symbols('r x y')
T=lambda n:sum((n-1-j)*r**j for j in range(n-1))
A=T(6)/(r+2);B=T(10)/(r+2)
DA=3*(r*r+r+1)*(r*r+3*r+1)
K=14*r**9+84*r**8+204*r**7+324*r**6+354*r**5+294*r**4+189*r**3+84*r**2+24*r+4
assert s.cancel(s.diff(A,r)*(r+2)**2-DA)==0
assert s.cancel((s.diff(B,r,2)*s.diff(A,r)-s.diff(B,r)*s.diff(A,r,2))*(r+2)**4-6*r*(r+2)*K)==0
assert [A.subs(r,0),A.subs(r,1)]==[s.Rational(5,2),5]
P=13*x**8-x**7*y-180*x**7-8*x**6*y+1265*x**6+87*x**5*y-5470*x**5+12*x**4*y**2-344*x**4*y+15450*x**4-42*x**3*y**2+581*x**3*y-28454*x**3-9*x**2*y**2+186*x**2*y+32020*x**2+5*x*y**3+102*x*y**2-1495*x*y-19200*x+y**4-22*y**3+30*y**2+850*y+4625
assert s.expand(s.resultant(T(6)-x*(r+2),T(10)-y*(r+2),r)-9*P)==0
assert s.cancel(P.subs({x:A,y:B}))==0
H=x**10+2*x**9-48*x**8-174*x**7+4061*x**6-21612*x**5+57612*x**4-86024*x**3+71010*x**2-28550*x+3625
assert s.expand(s.discriminant(P,y)+27*(x-2)**6*(x*x+40*x-100)*H**2)==0
hc=s.Poly(s.expand(H.subs(x,x+s.Rational(5,2))),x).all_coeffs()
assert all(v>0 for v in hc)
C=128*y**3-640*y**2+2400*y-8625
assert s.expand(P.subs(x,s.Rational(5,2))-(2*y-9)*C/256)==0
assert s.discriminant(s.diff(C,y),y)<0 and s.LC(s.Poly(s.diff(C,y),y))>0 and C.subs(y,s.Rational(9,2))==879
u,v,z=s.symbols('u v z')
Phi=s.Poly(s.cancel(u**8*P.subs({x:v/u,y:z/u})),u,v,z)
assert Phi.total_degree()==8 and all(sum(m)==8 for m,c in Phi.terms())
print('PASS positive A derivative and strict B(A^-1) curvature identities')
print('PASS exact resultant 9P and substitution P(A(r),B(r))=0')
print('PASS quartic discriminant identity; H(x)>0 for all x>=5/2 by positive shifted coefficients')
print('PASS endpoint root ordering: residual cubic strictly increasing, C(9/2)=879>0')
print('PASS Phi is a fixed homogeneous integer polynomial of degree8 in three logs')
(R/'three-log-certificate.json').write_text(json.dumps({'P':str(P),'H':str(H),'H_shift_5_over_2_descending':[str(v) for v in hc],'curvature_K':str(K),'Phi_terms':[[list(m),str(c)] for m,c in Phi.terms()]},indent=2)+'\n')
