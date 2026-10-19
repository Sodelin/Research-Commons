"""Finite algebra for ACTUAL-SIGNED-TAIL-PAIRING-20261019.md.

Contributor: dot (OpenAI), 19 October 2026.
Reconstructs all six actual channels with symbolic complete-filter moments.
Bath admission and continuous-time sign arguments are hand proofs, not
numerical bath integration or a full P5 certificate.
"""
import sympy as s

count = 0
def check(label, lhs, rhs):
    global count
    diff = s.simplify(lhs-rhs)
    zero = s.zeros(*diff.shape) if isinstance(diff, s.MatrixBase) else 0
    assert diff == zero, (label, diff)
    count += 1
    print('PASS', label)

I=s.eye(2)
X=s.Matrix([[0,1],[1,0]])
Y=s.Matrix([[0,-s.I],[s.I,0]])
Z=s.diag(1,-1)
P=s.kronecker_product(Z,Z)
O=s.kronecker_product(X,I)
B=s.kronecker_product(Y,Z)
b,bi,r,ri,q,qi,h=s.symbols('b bi r ri q qi h', real=True)
k0=b+s.I*bi
C=r+s.I*ri
D=q+s.I*qi
channels=[]
for site in range(2):
    for axis in [X,Y,Z]:
        A=s.kronecker_product(axis,I) if site==0 else s.kronecker_product(I,axis)
        K=k0*A if A*P==P*A else A*(C*s.eye(4)+s.I*D*P)
        channels.append((A,K))

def actual(F):
    result=s.I*h*(P*F-F*P)
    for A,K in channels:
        comm=A*F-F*A
        result+=comm*K-K.conjugate().T*comm
    return s.simplify(result)

check('six on-site channels', s.Integer(len(channels)), s.Integer(6))
check('actual identity annihilation', actual(s.eye(4)), s.zeros(4))
check('actual root action', actual(O), -4*(r+b)*O-(2*h+4*q)*B)
check('actual returned action', actual(B), (2*h+12*q)*O-4*(3*r+b)*B)
check('root scalar output vanishes in this subspace', s.trace(actual(O)), 0)
check('returned scalar output vanishes in this subspace', s.trace(actual(B)), 0)

# f=(u,-v). In these coordinates the full actual dynamics is N(u,v).
a,e,c,d=s.symbols('a e c d', positive=True)
N=s.Matrix([[-a,-c],[d,-e]])
centered=N+(a+e)*s.eye(2)/2
omega2=(e-a)**2-4*c*d
check('exact centered-square exponential identity', centered**2, omega2*s.eye(2)/4)
check('actual integrated positive coefficients', (-N).inv()*s.Matrix([1,0]),
      s.Matrix([e,d])/(a*e+c*d))
check('discriminant versus decay determinant', (a+e)**2-omega2, 4*(a*e+c*d))

at,qt,u,v=s.symbols('a_tail q_tail u v', real=True)
T=s.Matrix([[4*at,12*qt],[-4*qt,12*at]])
pairing=(s.Matrix([[1,-1]])*T*s.Matrix([u,-v]))[0]
check('signed tail directional pairing', pairing, 4*(at+qt)*u+12*(at-qt)*v)
integral=pairing.subs({u:e/(a*e+c*d),v:d/(a*e+c*d)})
check('integrated signed tail pairing', integral,
      4*(at*(e+3*d)+qt*(e-3*d))/(a*e+c*d))

full=s.Matrix([[-4*(r+b),2*h+12*q],[-2*h-4*q,-4*(3*r+b)]])
bt,rt=s.symbols('b_tail r_tail', real=True)
tail=full.subs({b:bt,r:rt,q:qt,h:0})-s.diag(-8*bt,-16*bt)
check('tail matrix from all-channel full filters', tail.subs(rt,bt-at), T)
check('returned coefficient margin at h=b',
      (4*(3*r+b)-3*(2*h+4*q)).subs(b,h), 12*r-2*h-12*q)

disc_lower=64*s.Rational(99,100)**2-4*(2+s.Rational(12,96))*(2+s.Rational(4,96))
assert disc_lower>0
check('positive exact discriminant lower bound', disc_lower, s.Rational(1361167,30000))
margin_lower=12*s.Rational(99,100)-2-s.Rational(12,96)
assert margin_lower>0
check('positive exact integrated q-tail coefficient lower bound', margin_lower, s.Rational(1951,200))

cc=s.symbols('cc', positive=True)
bath_a=s.pi**2/(768*s.sqrt(2)*cc)
gamma=2*s.sqrt(2)*cc/s.pi
tau=2*bath_a/s.pi
check('inherited bath x', gamma*tau, s.Rational(1,192))
check('inherited h times tau', (cc/2)*tau, s.pi/(768*s.sqrt(2)))
check('full-filter real-moment lower estimate', 1-4*s.Rational(1,192)**2,
      s.Rational(9215,9216))
assert s.Rational(9215,9216)>s.Rational(99,100)
z=s.symbols('z', positive=True)
check('real bath profile exponential representation',
      (s.cosh(z)/s.cosh(2*z)).rewrite(s.exp),
      s.exp(-z)*(1+s.exp(-2*z))/(1+s.exp(-4*z)))
print(f'PASS: {count} exact finite checks; no bath quadrature or master response certification.')
