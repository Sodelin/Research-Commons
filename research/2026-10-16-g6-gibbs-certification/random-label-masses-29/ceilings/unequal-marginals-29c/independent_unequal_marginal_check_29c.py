"""Independent bounded exact diagnostics for candidate29C.

Full labeled product laws are enumerated, including zero and unequal masses.
These finite checks do not replace the all-size hand proof or imported theorem.
"""
from fractions import Fraction as F
from itertools import product
from math import exp
from pathlib import Path
from hashlib import sha256

path=Path(__file__).with_name('P1-UNEQUAL-MARGINAL-ALPHABET-CEILING-29C.md')
expected='f4079e11dc031c41a23873b67f1232bf511993326afbbf4ced2a74dd4bb0c441'
assert sha256(path.read_bytes()).hexdigest()==expected
print('PASS: reviewed source SHA256',expected)

mass_pairs=[
    ((F(1,2),F(1,2),F(0)),(F(1,2),F(1,2),F(0))),
    ((F(16,32),F(15,32),F(1,32)),(F(1,2),F(1,2),F(0))),
    ((F(7,16),F(9,16),F(0)),(F(1,2),F(1,2),F(0))),
    ((F(1),F(0),F(0)),(F(0),F(1),F(0))),
]
alpha,epsilon=F(1,2),F(1,4)
cases=signal_cases=0
for s in (3,5):
    ell,h,delta=F(1,s),F(1,2),alpha/s
    alphabet=((h,h),(ell,ell),(ell+delta,ell-delta),(ell-delta,ell+delta))
    for offset in range(8):
        types=[[(offset+i+j)%4 if offset>=4 else offset for j in range(s)] for i in range(3)]
        b=[sum(t>=2 for t in row) for row in types]
        for pi,nu in mass_pairs:
            assert sum(pi)==sum(nu)==1
            full=F(0)
            for i in range(3):
                for bits in product((0,1),repeat=s):
                    p=q=F(1)
                    for bit,t in zip(bits,types[i]):
                        pp,qq=alphabet[t]
                        p*=pp if bit else 1-pp
                        q*=qq if bit else 1-qq
                    full+=abs(pi[i]*p-nu[i]*q)
            d=sum(abs(p-q) for p,q in zip(pi,nu))
            w=[min(p,q) for p,q in zip(pi,nu)]
            overlap=sum(wi*bi for wi,bi in zip(w,b))
            assert full<=d+4*delta*overlap
            assert sum(p*q/(p+q) for p,q in zip(pi,nu) if p+q)<=F(1,2)
            if full>=epsilon and d<epsilon/2:
                a=epsilon/(16*alpha)
                assert overlap/s>=2*a
                J=[i for i in range(3) if F(b[i],s)>=a]
                assert sum(w[i] for i in J)>=a
                signal_cases+=1
            cases+=1
print('PASS:',cases,'exact full-row L1 and pooled harmonic-mass cases;',signal_cases,'overlap-signal cases')

assert F(1,4)/9==F(1,36)
assert F(1,36)/8==F(1,288)
assert F(1,36)/4==F(1,144)
assert F(144**2,2)==10368
assert F(10368,10**12)<F(11,10**9)
assert F(2,3)-F(1,1000)>F(1,2)+F(4,25)
assert exp(-2*201*(4/25)**2)<1/100
assert 201*4==804 and 201*2==402
assert 2*(8*402)==6432
assert F(99,100)*16/8>1
assert F(99,100)*(8*402)/8>397
print('PASS: threshold, amplification, fixed-budget and physical retention constants')
print('SCOPE: bounded exact diagnostics; no physical simulation or Lean verification')
