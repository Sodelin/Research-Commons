"""Finite exact controls for SUPPORT-RESOLVED-PAULI-REFERENCE-20261019.md.
Contributor: dot (OpenAI), 19 October 2026. No full-filter or volume-limit run.
"""
from itertools import product
from fractions import Fraction
import sympy as s
checks=0
def check(name,a,b):
    global checks
    d=s.simplify(a-b)
    zero=s.zeros(*d.shape) if isinstance(d,s.MatrixBase) else 0
    assert d==zero,(name,d)
    checks+=1; print('PASS',name)
g,h,k,t=s.symbols('g h k t',positive=True)
M=s.Matrix([[-g,-2*h],[2*h,-k*g]])
a=(k+1)*g/2; d2=(k-1)**2*g*g-16*h*h
J=M+a*s.eye(2)
check('two-sector shifted square',J*J,d2*s.eye(2)/4)
ints=-M.inv()*s.Matrix([1,0])
check('two-sector integrated u',ints[0],k*g/(k*g*g+4*h*h))
check('two-sector integrated b',ints[1],2*h/(k*g*g+4*h*h))
check('two-sector weighted response',4*(ints[0]+k*ints[1]),4*k*(g+2*h)/(k*g*g+4*h*h))
check('five-over-g endpoint',4*(1+2*s.Rational(1,8)),5)
I=s.eye(2); X=s.Matrix([[0,1],[1,0]]); Y=s.Matrix([[0,-s.I],[s.I,0]]); Z=s.diag(1,-1)
kron=lambda *a:s.kronecker_product(*a)
u,b=s.symbols('u b',real=True)
F=u*kron(X,I,I)-b*kron(Y,Z,Z)
for name,A,target in [('root X',kron(X,I,I),4*b*b),('root Y',kron(Y,I,I),4*u*u),('root Z',kron(Z,I,I),4*(u*u+b*b)),('spectator X',kron(I,X,I),4*b*b),('spectator Z',kron(I,Z,I),0)]:
    C=A*F-F*A
    check('commutator square '+name,C.conjugate().T*C,target*s.eye(8))

# Single-site multiplication with phases in {1,i,-1,-i} encoded modulo four.
def mul(a,b):
    if a==0:return b,0
    if b==0:return a,0
    if a==b:return 0,0
    if (a,b) in [(1,2),(2,3),(3,1)]:return 6-a-b,1
    return 6-a-b,3

def prodword(a,b):
    out=[]; phase=0
    for x,y in zip(a,b):
        z,p=mul(x,y);out.append(z);phase+=p
    return tuple(out),phase%4

def transition(Q,P):
    T,p=prodword(Q,P); _,r=prodword(P,Q)
    if p==r:return None
    assert (p-r)%4==2
    # i*(i^p-i^r) is a real number +/-2.
    coefficient={1:-2,3:2}[p]
    return T,coefficient
pairs=0
for n in range(1,5):
    words=list(product(range(4),repeat=n))
    for Q in words:
        for P in words:
            T=transition(Q,P)
            if T is not None:
                out,c=T
                assert any(out) and abs(c)==2
                assert any(x and y for x,y in zip(Q,P))
            pairs+=1
checks+=1;print('PASS',pairs,'Pauli-pair transition rules through four sites')

words=list(product(range(4),repeat=3))
terms=[((1,3,0),Fraction(1,3)),((0,2,3),Fraction(1,3)),((3,0,1),Fraction(1,3))]
inc=max(sum(abs(j) for Q,j in terms if Q[i]) for i in range(3))
assert inc==Fraction(2,3)
for P in words:
    support=sum(bool(x) for x in P)
    col={}
    for Q,j in terms:
        z=transition(Q,P)
        if z is not None:
            out,c=z;col[out]=col.get(out,0)+c*j
    assert sum(abs(c) for c in col.values())<=2*inc*support
    assert -8*support+sum(abs(c) for c in col.values())<=-(8-2*inc)*support
checks+=1;print('PASS noncommuting three-term reference: all 64 coefficient columns')

# Product of three CZ factors, no dense 128 by 128 matrix needed.
pair_terms=[((0,0),Fraction(1,2)),((3,0),Fraction(1,2)),((0,3),Fraction(1,2)),((3,3),Fraction(-1,2))]
terms7=[]
for selected in product(pair_terms,repeat=3):
    word=(3,)+sum((term[0] for term in selected),())
    c=Fraction(1)
    for _,coef in selected:c*=coef
    terms7.append((word,c))
assert len({P for P,c in terms7})==64
assert sum(abs(c) for P,c in terms7)==8
for bits in product((1,-1),repeat=6):
    value=Fraction(0)
    for P,c in terms7:
        z=c
        for axis,sign in zip(P[1:],bits):
            if axis:z*=sign
        value+=z
    assert abs(value)==1
O=(1,0,0,0,0,0,0)
outputs={}
for Q,c in terms7:
    z=transition(Q,O);assert z is not None
    P,fac=z;outputs[P]=outputs.get(P,0)+fac*c
assert len(outputs)==64 and O not in outputs
assert sum(abs(c) for c in outputs.values())==16
checks+=1;print('PASS seven-site CZ-product: operator norm 1, J=8, outgoing coefficient norm 16')
check('positive coefficient derivative at g=8h',-8+sum(abs(c) for c in outputs.values()),8)

v,T,tau,gamma=s.symbols('v T tau gamma',positive=True)
r,ss=s.symbols('r ss',nonnegative=True)
check('finite-window transport integral',s.integrate(2*gamma*(s.exp(v*r)-1),(r,0,T))/T,2*gamma*((s.exp(v*T)-1)/(v*T)-1))
check('finite-window first r moment',s.integrate(4*gamma*h*r,(r,0,T))/T,2*gamma*h*T)
check('bath first moment',s.integrate(gamma*ss*s.exp(-ss/tau)/tau,(ss,0,s.oo)),gamma*tau)
c=2*h
bath_a=s.pi**2/(8*s.sqrt(2)*h*12*7*2**7)
check('seven-site original bath box',(2*s.sqrt(2)*c/s.pi)*(2*bath_a/s.pi),s.Rational(1,12*7*2**7))
check('seven-site original noise floor',(s.pi/(4*s.sqrt(2)))*(2*s.sqrt(2)*c/s.pi),h)
print('PASS:',checks,'finite controls; no full-filter q1 admission or P5 closure certified.')
