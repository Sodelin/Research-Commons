"""Independent all-n Taylor transcription from the labelled routing cases."""
import sympy as S,json
from pathlib import Path
n,r,z,e,W=S.symbols('n r z e W');Q=S.Rational
lam=lambda j:j*(j-1)/2
# Only the indicated orders can contribute through epsilon^4.
# At n=4 the j=1 cases do not exist and their multiplicity is zero.
U2=1-r;U3=(r-r**3)/2
V3=Q(1,3)-r/2+r**3/6;V4=r/10-r**3/6+r**6/15
Uy=lambda j:z*e-(j-1)**2*z**2*e**2/2
Vy=lambda j:z**2*e**2/2-(lam(j)+lam(j-1)+lam(j-2))*z**3*e**3/6
Dy=lambda j:1-lam(j)*z*e
j0=2*(e**2*(1-(n-2)*e)*U2*Uy(n-2)-e**3*(1-(n-3)*e)*V3*Dy(n-3)-e*(1-(n-1)*e)*Vy(n-1))
j1=2*(n-4)*(e**3*U3*(z*e)-e**4*V4-e**2*r*(z**2*e**2/2))
cubic=S.expand(j0+j1).coeff(e,3);quartic=S.factor(S.expand(j0+j1).coeff(e,4))
P=r**3+6*r*z-3*r+3*z**2-6*z+2
assert S.factor(cubic+P/3)==0
assert S.factor(S.expand(j0).coeff(e,4).subs(n,4)-quartic.subs(n,4))==0
rows=[]
for zz,ww,low,high in [(Q(3,8),9*(17*n+49)/2560,Q(459,10240),-Q(459,10240)),(Q(9,8),9*(143*n+71)/2560,-Q(3861,10240),Q(3861,10240))]:
 c3=cubic.subs({r:Q(1,4),z:zz});assert S.factor(c3)==0
 # Polynomial survival changes log-duration by (W+z^2/2)e^2.
 adjustment=S.diff(cubic,z).subs({r:Q(1,4),z:zz})*(ww+zz**2/2)
 actual=S.factor(quartic.subs({r:Q(1,4),z:zz})+adjustment)
 next_actual=S.factor(quartic.subs(n,n+2).subs({r:Q(1,4),z:zz})+adjustment)
 assert actual==low and next_actual==high
 rows.append({'Z':str(zz),'W_n':str(ww),'C_n':str(actual),'C_n_plus_2_using_same_W':str(next_actual),'product':str(actual*next_actual)})
print(json.dumps({'status':'PASS_UNIFORM_SYMBOLIC_TAYLOR_TRANSCRIPTION','cubic':str(S.factor(cubic)),'quartic':str(quartic),'n4_j1_absence_checked':True,'families':rows,'meaning':'Symbolic n is not bounded; local forest controls do not supply uniformity.'},indent=2))
