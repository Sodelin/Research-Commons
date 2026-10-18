"""Exact algebra controls plus explicitly noncertifying sector diagnostics.

No external downloads, simulation claim, or asymptotic proof by numerics.
The parameterized argument is in P1-FULL-LOCAL-SPAN-SIGNAL-CANDIDATE-34.md.
"""
from itertools import product
import sympy as sp
import mpmath as mp

I = sp.eye(2)
X = sp.Matrix([[0, 1], [1, 0]])
Y = sp.Matrix([[0, -sp.I], [sp.I, 0]])
Z = sp.diag(1, -1)
n = (I-Z)/2
for p0, q0 in product([-1, 1], repeat=2):
    B = (p0+q0)*X
    assert n*n == n
    assert B*B == 2*(1+p0*q0)*I
    assert (n*B+B*n)/2 == B/2
print("Exact operator identities: PASS (all four data-parity sectors)")

# Smallest admitted k: verify all 4^7 Pauli words, not only selected features.
# I/X/Y/Z represented by 0/1/2/3. The six data sites form two blocks of three.
k = 5
r = k-2
survivors = set()
for word in product(range(4), repeat=1+2*r):
    if sum(a != 0 for a in word) > k:
        continue
    med, data = word[0], word[1:]
    if any(a not in (0, 3) for a in data):
        continue  # data-Z twirl
    supports = []
    for block in (data[:r], data[r:]):
        bits = tuple(a == 3 for a in block)
        if any(bits[i] != bits[j] for i in range(r) for j in range(r)):
            break  # some even flip changes the sign
        supports.append(int(bits[0]))
    if len(supports) != 2:
        continue
    pbit, qbit = supports
    if (pbit+qbit+int(med in (1, 2))) % 2:
        continue  # Z_m times one flip in each block
    survivors.add((med, pbit, qbit))
expected = {(0,0,0), (3,0,0), (1,1,0), (1,0,1), (2,1,0), (2,0,1)}
assert survivors == expected
print("Full k=5 Pauli-span twirl: PASS; exchange leaves I,Z_m,X_m(P+Q),Y_m(P+Q)")
assert sp.re(sp.trace(X*Y)) == 0
assert sp.re(sp.trace(Z*Y)) == 0

p, q, c = sp.symbols('p q c', positive=True)
G = sp.Matrix([[2*c*c*(4*p+q), -2*c*(2*p+q)],
               [-2*c*(2*p+q), 2*(p+q)]])
v = sp.Matrix([4*c*c*(4*p-q), -8*c*(2*p-q)])
assert sp.factor(G.det()) == 4*c*c*p*q
limit = sp.factor((v.T*G.inv()*v)[0])
assert sp.simplify(limit - 8*c*c*(16*p**3-24*p**2*q+9*p*q**2+q**3)/(p*q)) == 0
print("Rescaled Gram determinant and inverse contraction: exact PASS")
print("R*q_good limiting expression:", limit)
x = sp.symbols('x', real=True)
assert sp.expand(2-(1-x)*(1+x)**2) == 1-x+x*x+x**3
print("Rare-sector scalar factor <=2 on [0,1]: exact polynomial PASS")

# These floating evaluations illustrate the exact formulas only.
mp.mp.dps = 80
def moments(beta, R, a):
    c = 1/(2*mp.sqrt(beta))
    D = mp.sqrt(a*a*R*R+16*c*c*R)
    # Stable rationalization of the lower eigenvalue.
    lm = -8*c*c*R/(a*R+D)
    lp = (a*R+D)/2
    em, ep, ea = mp.exp(-beta*lm), mp.exp(-beta*lp), mp.exp(-beta*a*R)
    den = 1+ea+em+ep
    wminus = (1-a*R/D)/2
    m = (ea+wminus*em+(1-wminus)*ep)/den
    b = -8*c*mp.sqrt(R)/D*(em-ep)/den
    return (em+ep)/den, m, b

for beta in (mp.mpf(1), mp.mpf('0.3')):
    pstar = mp.exp(2)/(1+mp.exp(2))
    qstar = mp.e/(1+mp.e)
    c0 = 1/(2*mp.sqrt(beta))
    exact_limit = 8*c0*c0*(16*pstar**3-24*pstar*pstar*qstar+9*pstar*qstar*qstar+qstar**3)/(pstar*qstar)
    for R in (128, 1024, 8192):
        p1,m1,b1 = moments(beta, R, mp.mpf('0.5'))
        p2,m2,b2 = moments(beta, R, mp.mpf(1))
        pbar,mbar,bbar = (p1+p2)/2,(m1+m2)/2,(b1+b2)/2
        cov = mp.matrix([[mbar-mbar*mbar, bbar/2-mbar*bbar],
                         [bbar/2-mbar*bbar, 4*pbar-bbar*bbar]])
        dv = mp.matrix([m1-m2,b1-b2])
        signal = (dv.T*cov**-1*dv)[0]
        assert mp.det(cov)>0 and signal>=0
        print("DIAGNOSTIC only: beta=%s R=%s trace-parity-lower=%s q_good=%s R*q_good=%s limiting=%s" %
              (beta,R,mp.nstr(2*abs(p1-p2),12),mp.nstr(signal,12),
               mp.nstr(R*signal,12),mp.nstr(exact_limit,12)))
print("Exact controls passed; numerical diagnostics are not interval certificates or an asymptotic proof.")
