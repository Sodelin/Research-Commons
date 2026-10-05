"""Exact algebra supporting the AB profile contract; no inverse/source run."""
import json
import sympy as s
fa,fr,ga,gr=s.symbols('fa fr ga gr')
D=s.det(s.Matrix([[fa,fr],[ga,gr]]))
assert s.simplify(ga-gr*fa/fr+D/fr)==0
c,Lmin,Lmax,dl,du=s.symbols('c Lmin Lmax dl du',positive=True)
ell=dl/(2*Lmax);U=2*(c+1/Lmin)/du
assert s.simplify(ell*Lmax-dl/2)==0
assert s.simplify(c/U+1/(U*Lmin)-du/2)==0
E,p,q,sv,v=s.symbols('E p q sv v')
M=E*p*(1-sv*v)+sv*E*v*q
assert s.expand(E-M-(E*(1-p)+E*p*sv*v-sv*E*v*q))==0
# The exact two-stage root/rate limits used for uniform profile existence.
z,a,T,R,r=s.symbols('z a T R r',positive=True)
B=s.exp(-z*T)*R/(R+z)
Mexpr=s.exp(-z*a)*r/(r+z)*(1-s.exp(-(r+z)*(T-a)))+s.exp(-r*(T-a))*B
assert s.simplify(Mexpr.subs(r,0)-B)==0
# Substitute positive length L before the infinity limit.
L=s.symbols('L',positive=True)
ML=s.simplify(Mexpr.subs(T,a+L))
assert s.simplify(s.limit(ML,r,s.oo)-s.exp(-z*a))==0
print(json.dumps({'status':'PASS','symbolic_identities':6,'scope':'Exact profile/bracket algebra only; strict inequalities remain hand-proved; no extra source or inverse execution.'},indent=2,sort_keys=True))
