"""Exact finite controls for NOISE-AWARE-REFERENCE-TRUNCATION-20261019.md.

Contributor: dot (OpenAI), 19 October 2026.
These controls do not prove the general operator argument or actual P5.
"""
import sympy as s

count = 0

def check(name, lhs, rhs):
    global count
    d = s.simplify(lhs-rhs)
    zero = s.zeros(*d.shape) if isinstance(d, s.MatrixBase) else 0
    assert d == zero, (name, d)
    count += 1
    print('PASS', name)

I=s.eye(2)
X=s.Matrix([[0,1],[1,0]])
Y=s.Matrix([[0,-s.I],[s.I,0]])
Z=s.diag(1,-1)
P=[I,X,Y,Z]
words=[s.kronecker_product(a,b) for a in P for b in P]
def matrix(fun):
    return s.Matrix(16,16,lambda i,j:s.simplify(s.trace(words[i]*fun(words[j]))/4))

axes=[s.kronecker_product(p,I) for p in P[1:]]
adj=[matrix(lambda F,A=A:A*F*A) for A in axes]
eye=s.eye(16)
E=(eye+sum(adj,s.zeros(16)))/4
Q=eye-E
check('partial expectation is idempotent',E*E,E)
check('oscillation Pauli decomposition',Q,3*eye/4-sum(adj,s.zeros(16))/4)
check('oscillation coefficient norm bound',s.Rational(3,4)+3*s.Rational(1,4),s.Rational(3,2))
check('three-axis reset normalization',2*sum((A-eye for A in adj),s.zeros(16)),8*(E-eye))
for j,A in enumerate(adj):
    check('reset commutes with Pauli map '+str(j),E*A-A*E,s.zeros(16))
check('reset restricted to oscillation', (E-eye)*Q,-Q)

hx,hy,hz=s.symbols('hx hy hz',real=True)
H=s.kronecker_product(hx*X+hy*Y+hz*Z,I)
C=matrix(lambda F:s.I*(H*F-F*H))
check('onsite coherent part commutes with reset',E*C-C*E,s.zeros(16))
Hout=s.kronecker_product(I,hx*X+hy*Y+hz*Z)
Cout=matrix(lambda F:s.I*(Hout*F-F*Hout))
check('exterior coherent part commutes with reset',E*Cout-Cout*E,s.zeros(16))

# Adjacent displayed hyperedges intersect on exactly one site and have Z/X there.
word_a=('X','Z','Z','I','I')
word_b=('I','X','I','Z','Z')
anti=sum(a!='I' and b!='I' and a!=b for a,b in zip(word_a,word_b))
check('adjacent three-body terms anticommute',anti,1)
check('root local incidence',9*s.Rational(1,9),1)
check('interior local incidence',(1+8)*s.Rational(1,9),1)
check('closed neighborhood',1+2*9,19)
check('forward branching',2*8,16)
for r in range(7):
    check('ball count depth '+str(r),1+18*sum(16**j for j in range(r)),s.Rational(6,5)*16**r-s.Rational(1,5))

h=s.symbols('h',positive=True)
c=2*h
b0=s.pi/(4*s.sqrt(2))
gamma=2*s.sqrt(2)*c/s.pi
a=s.pi**2/(8*s.sqrt(2)*h*(12*19*2**19))
tau=2*a/s.pi
check('bath noise coefficient',c/2,h)
check('original h noise ceiling',b0*gamma,h)
check('original bath envelope box',gamma*tau,s.Rational(1,12*19*2**19))
check('reference gap',8*c/2,8*h)

mu,alpha,theta,k=s.symbols('mu alpha theta k',positive=True)
F=2*theta*mu-alpha*(3+3*(k-1)*s.exp(mu)-theta)
check('optimized first derivative',s.diff(F,mu),2*theta-3*alpha*(k-1)*s.exp(mu))
mustar=s.log(2*theta/(3*alpha*(k-1)))
check('stationary point',s.diff(F,mu).subs(mu,mustar),0)
check('optimized maximum expression',F.subs(mu,mustar),2*theta*(mustar-1)+alpha*(theta-3))
check('three-body original-box test',F.subs({theta:8,k:3}),16*mu-alpha*(6*s.exp(mu)-5))

z=s.symbols('z',positive=True)
root=6*z-5
bulk=(16*z+1/z-14)/3
check('root minus bulk coefficient',root-bulk,(z-1)*(2*z+1)/(3*z))
check('root tangent sufficient test',16*mu-alpha*(6*(1+mu)-5),-alpha+(16-6*alpha)*mu)
bulk_lower=(16*(1+mu+mu**2/2)+(1-mu)-14)/3
check('bulk exponential tangent lower bound',bulk_lower,1+5*mu+s.Rational(8,3)*mu**2)
check('bulk quadratic certificate',16*mu-s.Rational(8,3)*bulk_lower,-s.Rational(64,9)*(mu-s.Rational(3,16))**2-s.Rational(29,12))
x=s.symbols('x',positive=True)
check('strict logarithm lower-bound derivative',s.diff(s.log(x)-2*(x-1)/(x+1),x),(x-1)**2/(x*(x+1)**2))
check('logarithm lower-bound anchor',(s.log(x)-2*(x-1)/(x+1)).subs(x,1),0)
check('log16 rational lower bound',4*s.Rational(2,3),s.Rational(8,3))
check('two-body original-box margin',8-3*2,2)
print('PASS:',count,'finite algebra controls. No actual Redfield response, bath integration, or general norm proof is execution-certified.')
