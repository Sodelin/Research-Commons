"""Exact scalar fixtures, not a proof assistant or cohomology calculation."""
from fractions import Fraction as Q
from itertools import product

def inputs(f, m, b, y, nc, log2x):
    assert f >= 1 and m >= 1 and b > 0 and y >= 1
    assert nc >= 0 and 0 <= log2x <= y
    return f*m*b*y*y + log2x*nc, y*(f*m*b*y + nc)

count = beyond_original = 0
for f,m,b,y,nc,a0,c,r in product(
    (1, 3), (1, 2), (Q(1,2),Q(4)), (Q(1),Q(3,2),Q(3)),
    (Q(0),Q(2)), (Q(0),Q(1,3),Q(1)), (Q(-3),Q(0),Q(7,3)), (0,1,5)
):
    a,h = inputs(f,m,b,y,nc,a0*y)
    assert b <= h and 0 <= a <= h
    for v in (Q(0), b, (b+h)/2, h):
        upper = r*(c*a+v)
        required = r*(abs(c)+1)*h
        assert upper <= required
        count += 1
        beyond_original += v > b
    # The sign-aware sufficient threshold is exact for the scalar link.
    vmax = (abs(c)+1)*h - c*a
    assert vmax >= h
    assert r*(c*a+vmax) == r*(abs(c)+1)*h
    if r > 0:
        assert r*(c*a+vmax+Q(1,100)) > r*(abs(c)+1)*h
a,h = inputs(1,1,Q(4),Q(2),Q(0),Q(2))
assert h==16 and h>4
assert h+Q(1,100)>h # C=0, rank=1, L=V violates the required conclusion.
print(f"{count} exact tests passed; {beyond_original} above the original b budget.")
print("Signed-C exact thresholds and scalar counterexamples above threshold checked.")
