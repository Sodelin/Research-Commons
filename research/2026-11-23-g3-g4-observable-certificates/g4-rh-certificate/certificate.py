"""Exact rational cap-four private equal-arm BOTH certificate fixtures."""
from fractions import Fraction as F
from math import comb
import unittest

N = 4

def e(q):
    # Upper-to-lower pure-death rates lambda_r = choose(r, 2).
    q = F(q)
    out = [[F(0) for _ in range(N+1)] for _ in range(N+1)]
    out[0][0] = 1
    for n in range(1, N+1):
        for k in range(1, n+1):
            rates = [comb(r, 2) for r in range(k, n+1)]
            for l in rates:
                num = 1
                for i in rates[1:]:
                    num *= i
                den = 1
                for i in rates:
                    if i != l:
                        den *= i-l
                out[n][k] += F(num, den)*q**l
    return out

def bigon(q, g):
    a = e(q)
    b = [[F(0) for _ in range(N+1)] for _ in range(N+1)]
    for n in range(N+1):
        for k in range(n+1):
            prob = comb(n,k)*g**k*(1-g)**(n-k)
            for i in range(k+1):
                for j in range(n-k+1):
                    b[n][i+j] += prob*a[k][i]*a[n-k][j]
    return b

def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(N+1))
             for j in range(N+1)] for i in range(N+1)]

def word(factors):
    K, C = e(1), F(1)
    for q, g in factors:
        K = mul(K, e(q) if g is None else bigon(q,g))
        C *= q
    return C,K

def classify_ordinary_common_face(C, p2, p3, p42):
    """Exact screen, assumes observed equal-arm private face and exact inputs.

    Rejects an impossible diagonal or an impossible one-fair-cell chronology.
    Otherwise gives a guaranteed one-cell descriptor only on equality, or unknown.
    The other response coordinates still have to match for transcript validation.
    """
    C,p2,p3,p42 = map(F, (C,p2,p3,p42))
    if not 0 < C < 1:
        raise ValueError("strict COMMON survival required")
    u = p2/C-1
    v = p3/C**3-1
    if u < 0 or v < 3*u+3*u*u or u >= (1/C-1)/2:
        return "excluded", None
    if u == 0:
        return ("ordinary", C) if v == 0 and p42 == e(C)[4][2] else ("excluded", None)
    if v != 3*u+3*u*u:
        return "unknown", None
    q = 1/(1+2*u)
    D = C/q
    p42_0 = mul(bigon(q,F(1,2)),e(D))[4][2]
    k = (1-q)**3/8
    z5 = 1-5*(p42-p42_0)/(k*D)
    if not D**5 < z5 < 1:
        return "excluded", None
    return "unique-equivalent-if-realized", (q,D,z5)

class Tests(unittest.TestCase):
    def test_ordinary_semigroup(self):
        self.assertEqual(mul(e(F(3,5)),e(F(2,3))),e(F(2,5)))
    def test_nonordinary_exact_recovery(self):
        x,q,y = F(2,3),F(1,2),F(3,5)
        C,K = word([(x,None),(q,F(1,2)),(y,None)])
        result = classify_ordinary_common_face(C,K[2][2],K[3][3],K[4][2])
        self.assertEqual(result, ("unique-equivalent-if-realized", (q,x*y,x**5)))
        C2,K2 = word([(y,None),(q,F(1,2)),(x,None)])
        self.assertEqual((C,K[2][2],K[3][3]),(C2,K2[2][2],K2[3][3]))
        self.assertNotEqual(K[4][2],K2[4][2])
    def test_biased_and_double_not_excluded_but_not_forced(self):
        for cells in [[(F(1,2),F(1,3))],[(F(1,2),F(1,2)),(F(2,3),F(1,2))]]:
            C,K = word([(F(2,3),None)]+cells+[(F(3,5),None)])
            self.assertEqual(classify_ordinary_common_face(C,K[2][2],K[3][3],K[4][2]),("unknown",None))
    def test_infeasible_observed_data(self):
        C,K = word([(F(2,3),None),(F(1,2),F(1,2)),(F(3,5),None)])
        self.assertEqual(classify_ordinary_common_face(C,K[2][2],K[3][3]-F(1,1000),K[4][2]),("excluded",None))
        self.assertEqual(classify_ordinary_common_face(C,K[2][2],K[3][3],F(0)),("excluded",None))
    def test_exact_commutator(self):
        G = [[F(0) for _ in range(N+1)] for _ in range(N+1)]
        for n in range(2, N+1):
            G[n][n] = -comb(n, 2)
            G[n][n-1] = comb(n, 2)
        for q in (F(1,9),F(1,3),F(1,2),F(13,17)):
            B = bigon(q, F(1,2))
            GB, BG = mul(G,B), mul(B,G)
            expected = [[F(0) for _ in range(N+1)] for _ in range(N+1)]
            expected[4][2] = (1-q)**3/8
            expected[4][1] = -expected[4][2]
            self.assertEqual([[GB[i][j]-BG[i][j] for j in range(N+1)]
                              for i in range(N+1)],expected)
    def test_exact_chronology_grid(self):
        for q in (F(1,9),F(1,3),F(1,2),F(13,17)):
            for x in (F(1,5),F(3,7),F(6,7)):
                for y in (F(1,8),F(2,3),F(5,7)):
                    C,K = word([(x,None),(q,F(1,2)),(y,None)])
                    expected = ("unique-equivalent-if-realized",(q,x*y,x**5))
                    self.assertEqual(classify_ordinary_common_face(C,K[2][2],K[3][3],K[4][2]),expected)

if __name__ == "__main__":
    unittest.main(verbosity=2)
