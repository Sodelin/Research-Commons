"""Exact summaries for the v2 G4 gap bound; root-count fixtures reuse v1."""
from fractions import Fraction as F
from math import comb, prod
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "g4-rh-certificate"))
from certificate import e, word

def gap_certificate(common_pair, common_triple, independent_pair, independent_triple):
    """On the verified equal-arm private face, return exact stability bounds.

    "certified" requires the data are from a physical word; this function is
    not an admissibility test for all rows. Coin deviation bound is squared.
    """
    c, c3, p2, p3 = map(F, (common_pair, common_triple, independent_pair, independent_triple))
    if not 0 < c < 1 or c3 != c**3:
        return "outside-face", None
    u, v = p2/c - 1, p3/c**3 - 1
    delta = v - 3*u - 3*u*u
    if u < 0 or delta < 0 or u >= (1/c-1)/2 or (u == 0 and v != 0):
        return "excluded", None
    if u == 0:
        return "ordinary", None
    r = u/(4*(1+u))
    if delta >= 3*u*r*r:
        return "no-bound-of-this-form", None
    tail = delta/(3*u*r)
    dominant_min = max(r, (u-tail)/(1+tail))
    return "certified", {
        "U": u, "delta": delta, "dominant_min": dominant_min,
        "tail_max": tail, "bias_squared_max": delta/(12*dominant_min**2),
        "weighted_bias_squared_max": delta/12,
    }

def diag(factors):
    c, k = word(factors)
    return c, c**3, k[2][2], k[3][3]

def components(factors):
    return [(2*g*(1-g)*(1/q-1),g) for q,g in factors if g is not None]

def dominates(factors):
    cells = components(factors)
    i = max(range(len(cells)), key=lambda j: cells[j][0])
    m,g = cells[i]
    tail = prod(1+u for j,(u,_) in enumerate(cells) if j != i)-1
    weighted = sum(u*u*(g-F(1,2))**2 for u,g in cells)
    return m,g,tail,weighted

def count_tv(k1,k2,n):
    return sum(abs(x-y) for x,y in zip(k1[n],k2[n]))/2

class Tests(unittest.TestCase):
    edges = [(F(2,3),None)],[(F(3,5),None)]
    def fixture(self, cells):
        return self.edges[0] + cells + self.edges[1]

    def test_one_fair_has_zero_gap(self):
        f = self.fixture([(F(1,2),F(1,2))])
        s,b = gap_certificate(*diag(f))
        self.assertEqual(s,"certified")
        self.assertEqual((b["delta"],b["tail_max"],b["bias_squared_max"]),(0,0,0))

    def test_many_tiny_cells_do_not_fake_near_equality(self):
        f = self.fixture([(F(99,100),F(1,2))]*50)
        s,b = gap_certificate(*diag(f))
        self.assertEqual(s,"no-bound-of-this-form")
        c,_,p2,p3 = diag(f)
        U = p2/c-1
        R = U/(4*(1+U))
        self.assertTrue(all(u<R for u,_ in components(f)))
        self.assertGreaterEqual(p3/c**3-1-3*U-3*U*U,3*U*R*R)

    def test_weak_rare_cell_retains_large_clock(self):
        q,g = F(1,3), F(1,10**6)
        x,y = self.edges
        f = x + [(q,g),(F(1,2),F(5001,10000))] + y
        s,b = gap_certificate(*diag(f))
        self.assertEqual(s,"certified")
        m,gd,tail,wb = dominates(f)
        self.assertLessEqual(b["dominant_min"],m)
        self.assertLessEqual(tail,b["tail_max"])
        self.assertLessEqual((gd-F(1,2))**2,b["bias_squared_max"])
        self.assertLessEqual(wb,b["weighted_bias_squared_max"])
        comparison = x + [(q,None),(F(1,2),F(1,2))] + y
        c,k1 = word(f)
        c2,k2 = word(comparison)
        self.assertEqual(c,c2)
        for n in range(1,5):
            self.assertLessEqual(count_tv(k1,k2,n),comb(n,2)*tail+n*abs(gd-F(1,2)))

    def test_group_gap_and_bias_inequalities_exact_grid(self):
        for qs in [(F(1,2),F(2,3)),(F(99,100),F(1,5)),(F(1,3),F(1,3))]:
            for gs in [(F(1,2),F(1,2)),(F(1,3),F(2,3)),(F(3,7),F(1,2))]:
                f = self.fixture(list(zip(qs,gs)))
                c,_,p2,p3 = diag(f)
                U = p2/c-1
                delta = p3/c**3-1-3*U-3*U*U
                (a,g),(b,h) = components(f)
                self.assertGreaterEqual(delta,3*a*b*(U+a*b))
                self.assertGreaterEqual(delta,12*(a*a*(g-F(1,2))**2+b*b*(h-F(1,2))**2))

    def test_negative_gap_excluded_and_wrong_face_not_certified(self):
        c,c3,p2,p3 = diag(self.fixture([(F(1,2),F(1,2))]))
        self.assertEqual(gap_certificate(c,c3,p2,p3-F(1,1000))[0],"excluded")
        self.assertEqual(gap_certificate(c,c3+F(1,1000),p2,p3)[0],"outside-face")

if __name__ == "__main__":
    unittest.main(verbosity=2)
