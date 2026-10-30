"""Formal algebra checks only; no free-profile feasibility/sign experiment."""
import sympy as s
n=4
x=s.symbols('x0:4'); t=s.symbols('t0:4'); e=s.symbols('e0:4'); delta=s.symbols('d0:4')
y=[t[i]*x[i]+e[i] for i in range(n)]
Q=[sum(x[:i+1]) for i in range(n)]
raw=sum(x[i]*y[j] for i in range(n) for j in range(i+1,n))+sum(x[i]*y[i]/2+delta[i] for i in range(n))
rhs=t[-1]*Q[-1]**2/2-sum((t[i+1]-t[i])*Q[i]**2/2 for i in range(n-1))+sum(e[i]*(sum(x[:i])+x[i]/2)+delta[i] for i in range(n))
assert s.expand(raw-rhs)==0
f=[]; js=[]; pre=s.eye(3)
for i in range(3):
 a,b,c=s.symbols(f'a{i} b{i} c{i}', nonzero=True)
 x0,y0,z0=s.symbols(f'x{i} y{i} z{i}')
 D=s.diag(a,b,c); F=s.Matrix([[a,x0,z0],[0,b,y0],[0,0,c]])
 J=pre*(F*D.inv()-s.eye(3))*pre.inv()
 f.append(F);js.append(J);pre=pre*D
W=f[0]*f[1]*f[2]; V=W*pre.inv()
assert s.simplify(V[0,1]-sum(J[0,1] for J in js))==0
assert s.simplify(V[1,2]-sum(J[1,2] for J in js))==0
assert s.simplify(V[0,2]-sum(J[0,2] for J in js)-sum(js[i][0,1]*js[j][1,2] for i in range(3) for j in range(i+1,3)))==0
print('PASS: symbolic variable-weight quadratic WITH endpoint and profile/local residual terms; exact chronological diagonal-conjugation product.')
