"""Bounded exact algebra checks for the independent candidate29A review.

These are checks of means, thresholds and constants. They do not simulate
physical Gibbs states or prove concentration for unbounded sample sizes.
"""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path

source = Path(__file__).with_name('P1-RANDOM-LABEL-MASS-FAMILY-CEILING-29A.md')
expected = 'db4c8cfa0332c037acf89c89bdf8fc19e59aabf34d26700f11a66ba2f20e8e7c'
assert sha256(source.read_bytes()).hexdigest() == expected
print('PASS: reviewed source SHA256', expected)

cases = 0
for s in (10, 17, 32, 101):
    h, ell = F(1, 2), F(1, s)
    def f(x, y):
        return x*y-(h+ell)*(x+y)/2+h*ell
    assert [f(0,0), f(1,0), f(0,1), f(1,1)] == [ell/2, -F(1,4), -F(1,4), (1-ell)/2]
    for alpha in (F(1,2), F(1,4), F(1,16)):
        delta = alpha/s
        pairs = [(h,h,F(0)), (ell,ell,F(0)),
                 (ell+delta,ell-delta,-delta**2),
                 (ell-delta,ell+delta,-delta**2)]
        for p,q,want in pairs:
            mean = sum(f(x,y)*(p if x else 1-p)*(q if y else 1-q)
                       for x in (0,1) for y in (0,1))
            second = sum(f(x,y)**2*(p if x else 1-p)*(q if y else 1-q)
                         for x in (0,1) for y in (0,1))
            assert mean == want
            assert 0 <= second-mean**2 <= 1
            cases += 1
print('PASS: exact statistic means / variance bounds in', cases, 'cases')

# Exact algebraic constants in the hand proof.
assert F(1,2)*F(1,6)**2 == F(1,72)
assert F(1,144) == F(1,72)/2
assert F(1,576) == F(1,72)/8
assert F(1,3)*F(1,144) == 2*F(1,864)
C = 10**7
q_C = F(3*864**2*1600**3, C**3)
assert q_C < F(1,10**5)
assert F(99,100)*8/2 > 3  # ceil(2n)<=3n for n>=1
assert F(99,100)*8/8 > F(1,2)  # physical shortage exponent
print('PASS: occupancy, threshold, Chebyshev and retention constants')
print('q_C =', q_C, '=', float(q_C))
print('SCOPE: finite exact diagnostics; all-size statements use the accompanying hand proof')
