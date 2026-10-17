"""Exact finite checks supplementing, not replacing, candidate29C's proof."""
from fractions import Fraction as F
from itertools import product
import sympy as sp

p, q, ell, h, delta = sp.symbols('p q ell h delta', real=True)
mean = p*q - (h+ell)*(p+q)/2+h*ell
assert sp.factor(mean.subs({p:h, q:h})) == 0
assert sp.factor(mean.subs({p:ell, q:ell})) == 0
assert sp.factor(mean.subs({p:ell+delta, q:ell-delta})+delta**2) == 0

n, s, D, L, a, alpha = sp.symbols('n s D L a alpha', positive=True)
m0 = a**2*n**2/(36*D*L)
tau = a*alpha**2*m0/(4*s)
noise = sp.factor(s*n/(2*tau**2))
assert sp.simplify(noise-10368*s**3*D**2*L**2/(a**6*alpha**4*n**3)) == 0
assert F(10368, 10**12) < F(11, 10**9)
assert a*alpha**2*(m0/2)/s == 2*tau

# Exact geometric/normalization inequalities, including zero masses.
grids = [(F(x,100), F(100-x,100)) for x in (0,25,49,50,51,75,100)]
pooled_cases = 0
for pi, nu in product(grids, repeat=2):
    assert sum(x*y/(x+y) if x+y else 0 for x,y in zip(pi,nu)) <= F(1,2)
    for ks in product((1,2,5,11), repeat=2):
        for mask in ((1,0),(0,1),(1,1)):
            used = [i for i in range(2) if mask[i]]
            lhs = sum(pi[i]*nu[i]/ks[i] for i in used)
            rhs = sum(min(pi[i],nu[i]) for i in used)**2/sum(ks[i] for i in used)
            assert lhs >= rhs
            pooled_cases += 1

def row_law(parameters):
    law = []
    for bits in product((0,1), repeat=len(parameters)):
        value = F(1)
        for bit, parameter in zip(bits, parameters):
            value *= parameter if bit else 1-parameter
        law.append(value)
    assert sum(law) == 1
    return law

dim=3
alph=F(1,4)
lo=F(1,dim)
de=alph/dim
alphabet=((F(1,2),F(1,2)),(lo,lo),(lo+de,lo-de),(lo-de,lo+de))
profiles=list(product(range(4), repeat=dim))
records=[]
for prof in profiles:
    ps=[alphabet[j][0] for j in prof]
    qs=[alphabet[j][1] for j in prof]
    records.append((row_law(ps),row_law(qs),sum(j>=2 for j in prof)))

l1_cases=overlap_cases=0
for index, left in enumerate(records):
    right=records[(17*index+13)%len(records)]
    for pi,nu in product(grids,repeat=2):
        ds=sum(abs(x-y) for x,y in zip(pi,nu))
        ww=[min(x,y) for x,y in zip(pi,nu)]
        rows=(left,right)
        dist=sum(abs(pi[i]*pr-nu[i]*qr) for i,(pl,ql,b) in enumerate(rows)
                 for pr,qr in zip(pl,ql))
        bcounts=[rec[2] for rec in rows]
        assert dist<=ds+4*de*sum(w*b for w,b in zip(ww,bcounts))
        l1_cases+=1
        for eps in (F(1,8),F(1,16),F(1,32)):
            if dist>=eps and ds<eps/2:
                aa=eps/(16*alph)
                assert sum(w*F(b,dim) for w,b in zip(ww,bcounts))>=2*aa
                jj=[i for i,b in enumerate(bcounts) if F(b,dim)>=aa]
                assert sum(ww[i] for i in jj)>=aa
                overlap_cases+=1

# Universal one-cross-pair centering has only an antisymmetric linear part.
A,B,C,E,t=sp.symbols('A B C E t')
poly=sp.Poly(A*t*t+(B+C)*t+E,t)
sol=sp.solve(poly.all_coeffs(),(A,C,E),dict=True)
assert sol==[{A:0,C:-B,E:0}]

print('PASS: three symbolic alphabet means; exact signal/variance constants.')
print(f'PASS: {pooled_cases} rational unequal-mass Cauchy/normalization checks, including zeros.')
print(f'PASS: {l1_cases} complete-row L1 checks; {overlap_cases} eligible overlap-signal checks.')
print('PASS: symbolic one-cross-pair centering obstruction for arbitrary Bernoulli means.')
print('Scope: finite/symbolic checks only; no asymptotic theorem, physical encoding, or imported tester independently proved by this script.')
