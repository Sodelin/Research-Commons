"""Independent exact algebra controls; no finite-size/asymptotic certification by numerics."""
import sympy as s
I=s.eye(2); X=s.Matrix([[0,1],[1,0]]); n=s.diag(0,1)
a,R,c,A=s.symbols('a R c A', positive=True)
h=a*R*n+c*s.sqrt(R)*A*X
D=s.symbols('D',positive=True)
# The lower/upper spectral projectors for a two-level block.
V=h-a*R*I/2
assert s.simplify(V*V-(a*a*R*R/4+c*c*R*A*A)*I)==s.zeros(2)
Pminus=I/2-V/D
assert s.simplify(s.trace(n*Pminus)-(1-a*R/D)/2)==0
assert s.simplify(s.trace(A*X*Pminus)+2*c*s.sqrt(R)*A*A/D)==0
print('Exact general two-level expectations: PASS')
p,q=s.symbols('p q',positive=True)
G=s.Matrix([[2*c*c*(4*p+q),-2*c*(2*p+q)],[-2*c*(2*p+q),2*(p+q)]])
assert s.factor(G.det())==4*c*c*p*q
print('Limiting Gram determinant: PASS')
u,v,rho,sigma=s.symbols('u v rho sigma',real=True)
t=(u+v)/2; theta=(u-v)/(u+v)
nu=((1+theta)*rho+(1-theta)*sigma)/2
assert s.factor(u*rho-v*sigma-t*((1-theta**2)*(rho-sigma)+2*theta*nu))==0
print('Unequal good-block probabilities decomposition: PASS')
x=s.symbols('x',nonnegative=True)
assert s.expand(2-(1-x)*(1+x)**2)==1-x+x*x+x**3
l=s.symbols('l',nonnegative=True)
expr=(2-a)*R+2*l*(R-l)+(2*a-2)*l-(R+(R-1)*l)
assert s.expand(expr-((1-a)*R+l*(R-2*l+2*a-1)))==0
print('Rare-sector scalar and all-minus-phase remainder identities: PASS')
print('These controls supplement a hand proof, not a P1 testing lower bound or Lean verification.')
