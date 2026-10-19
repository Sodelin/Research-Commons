"""Finite exact algebra for KAM-DRESSING-ADMISSION-20261019.md.

Contributor: dot (OpenAI), 19 October 2026.
Checks the complete two-site actual-filter generator and Liouville blocks.
It does not certify the bath integrals, KAM convergence, or uniform P5.
"""
import sympy as sp

count = 0
def check(name, a, b):
    global count
    d = sp.simplify(a-b)
    z = sp.zeros(*d.shape) if isinstance(d, sp.MatrixBase) else 0
    assert d == z, (name, d)
    count += 1
    print('PASS', name)

I = sp.eye(2)
X = sp.Matrix([[0,1],[1,0]])
Y = sp.Matrix([[0,-sp.I],[sp.I,0]])
Z = sp.diag(1,-1)
paulis = [I,X,Y,Z]
b, bi, cr, ci, sr, si, h = sp.symbols('b bi cr ci sr si h', real=True)
k0, C, D = b+sp.I*bi, cr+sp.I*ci, sr+sp.I*si
P = sp.kronecker_product(Z,Z)
words = [sp.kronecker_product(a,d) for a in paulis for d in paulis]
channels = []
for site in range(2):
    for axis in paulis[1:]:
        A = sp.kronecker_product(axis,I) if site == 0 else sp.kronecker_product(I,axis)
        if A*P-P*A == sp.zeros(4):
            K = k0*A
        else:
            check('channel anticommutes with H', A*P+P*A, sp.zeros(4))
            K = A*(C*sp.eye(4)+sp.I*D*P)
        channels.append((A,K))

def actual(F):
    ans = sp.I*h*(P*F-F*P)
    for A,K in channels:
        c = A*F-F*A
        ans += c*K-K.conjugate().T*c
    return sp.simplify(ans)

def frozen(F):
    return sp.simplify(sum((2*b*(A*F*A-F) for A,K in channels), sp.zeros(4)))

R = sp.Matrix(16,16,lambda i,j: sp.simplify(sp.trace(words[i]*actual(words[j]))/4))
B = sp.Matrix(16,16,lambda i,j: sp.simplify(sp.trace(words[i]*frozen(words[j]))/4))
check('all six channels present', len(channels), 6)
check('actual identity annihilation', R[:,0], sp.zeros(16,1))
check('frozen one-site gap', B[4,4], -8*b)
check('frozen two-site gap', B[15,15], -16*b)
check('actual root X action', actual(words[4]), -4*(cr+b)*words[4]-(2*h+4*sr)*words[11])
check('actual root Y action', actual(words[8]), -4*(cr+b)*words[8]+(2*h+4*sr)*words[7])

# The neutral projection on site 1 is QTQ - T_00 Q; the creation
# projection on site 2 is QTP.  R(I)=0 makes the subtraction below zero.
NC = sp.zeros(16)
CN = sp.zeros(16)
for a1 in range(1,4):
    for a2 in range(1,4):
        for d1 in range(1,4):
            NC[4*a1+a2,4*d1] = R[4*a1+a2,4*d1] - (R[a2,0] if a1 == d1 else 0)
        for d2 in range(1,4):
            CN[4*a1+a2,d2] = R[4*a1+a2,d2] - (R[4*a1,0] if a2 == d2 else 0)
expected_NC = sp.zeros(16)
expected_NC[11,4] = -(2*h+4*sr)
expected_NC[7,8] = 2*h+4*sr
expected_CN = sp.zeros(16)
expected_CN[14,1] = -(2*h+4*sr)
expected_CN[13,2] = 2*h+4*sr
check('neutral-creation component', NC, expected_NC)
check('creation-neutral component', CN, expected_CN)
proj = sp.zeros(16); proj[4,4]=1; proj[8,8]=1
check('NC singular values squared', NC.T*NC, (2*h+4*sr)**2*proj)
proj = sp.zeros(16); proj[1,1]=1; proj[2,2]=1
check('CN singular values squared', CN.T*CN, (2*h+4*sr)**2*proj)
check('frozen terms do not enter NC', B[11,4], 0)
check('guard excess at h=b', (2*(2*h+4*sr)-8*b/2).subs(h,b), 8*sr)

c = sp.symbols('c', positive=True)
a = sp.pi**2/(768*sp.sqrt(2)*c)
gamma, tau, b0 = 2*sp.sqrt(2)*c/sp.pi, 2*a/sp.pi, sp.pi/(4*sp.sqrt(2))
check('bath noise product', gamma*tau, sp.Rational(1,192))
check('original box ceiling', sp.Rational(1,12*2*2**2), sp.Rational(1,96))
check('Hamiltonian at allowed strength', b0*gamma, c/2)

u = sp.symbols('u', positive=True)
profile = sp.cosh(u)/sp.cosh(2*u)
check('strictly decreasing real bath profile', sp.diff(profile,u),
      -sp.sinh(u)*(2*sp.cosh(u)**2+1)/sp.cosh(2*u)**2)
g = sp.symbols('g', positive=True)
A0 = sp.Matrix([[-g,2*h],[-2*h,-2*g]])
check('coherent-reference reduced inverse', (-A0).inv(),
      sp.Matrix([[2*g,2*h],[-2*h,g]])/(2*g**2+4*h**2))
check('coherent-reference dissipative part', -(A0+A0.T)/2, sp.diag(g,2*g))
print(f'PASS: {count} exact finite checks; no uniform response or KAM admission is certified.')
