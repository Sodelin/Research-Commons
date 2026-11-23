from fractions import Fraction
from math import isqrt

for n in (1000, 10001, 56789, 101921, 543210):
    a = isqrt(n)
    q = Fraction(n, a)
    for d in (Fraction(1, 5), Fraction(1, 10), Fraction(1, 17)):
        lower = (1-d)*q
        K = [k for k in range(lower.numerator//lower.denominator, (n-1)//a+1)
             if lower < k < q]
        pairs = [(k, j) for k in K for j in range(a+1, (n-1)//k+1)]
        assert all(1 <= n-k*j < d*n and a < j < a/(1-d) for k,j in pairs)
        assert len(pairs) <= (d*q+1)*(d*a/(1-d)+1)
        expected = sum(max(0, (n-1)//k - a) for k in K)
        assert expected == len(pairs)
        assert all(Fraction(1,k) <= 1/lower for k in K)
    print(f"N={n}: all three exact rectangle and support checks pass")
