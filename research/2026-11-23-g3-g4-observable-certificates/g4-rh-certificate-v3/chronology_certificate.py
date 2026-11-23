"""Conservative exact-arithmetic G4 positive-gap chronology intervals."""
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent/"g4-rh-certificate-v2"))
from gap_certificate import gap_certificate, diag, word
from certificate import bigon, e, mul

def sqrt_upper(v, scale=10**12):
    """Round a rational square root up, never down."""
    m = v.numerator * scale**2
    k = isqrt(m//v.denominator)
    return F(k + (k*k*v.denominator < m), scale)

def chronology_certificate(c, c3, p2, p3, p42):
    """Sound interval conditional on the original strict matched private face."""
    c, p42 = F(c), F(p42)
    if not 0 <= p42 <= 1:
        return "excluded", None
    state,b = gap_certificate(c,c3,p2,p3)
    if state == "ordinary":
        return ("ordinary",None) if p42 == e(c)[4][2] else ("excluded",None)
    if state != "certified":
        return state, None

    u, delta = b["U"], b["delta"]
    m, tail = b["dominant_min"], b["tail_max"]
    a0 = 1+2*u
    q0, D0 = 1/a0, c*a0
    a_minus = max(1+2*m, a0-2*(1+u)*tail)
    a_plus = min(1/c, a0+2*delta/(3*m))
    tau = max(a0-a_minus,a_plus-a0)/a_minus
    bv = b["bias_squared_max"]
    scale = max(10**12, 1+isqrt(bv.denominator//bv.numerator)) if bv else 10**12
    coin = min(F(1,2), sqrt_upper(bv,scale))
    eta = min(F(1), 6*(tail+2*tau)+4*coin)
    base = mul(bigon(q0,F(1,2)),e(D0))[4][2]
    K = D0*(1-q0)**3/40
    rhat = 1+(base-p42)/K
    rho = eta/K
    lo,hi = max(D0**5,rhat-rho), min(F(1),rhat+rho)
    # r = D0**(5s) is strictly between D0**5 and 1. Report a closed cover.
    if lo > hi or hi == D0**5 or lo == 1:
        return "excluded",None
    x5_lo = lo*min(F(1),(a_minus/a0)**5)
    x5_hi = min(F(1),hi*max(F(1),(a_plus/a0)**5))
    return "interval",{
        "q0":q0, "D0":D0, "r_interval":(lo,hi), "x5_interval":(x5_lo,x5_hi),
        "eta":eta, "tau":tau, "gap":delta, "K":K, "baseline":base,
        "fitted_x5":(lo+hi)/2, "clock_tv_coefficient":tail+2*tau+(hi-lo)/(5*lo),
        "coin_tv_coefficient":coin
    }

class Tests(unittest.TestCase):
    def test_rational_sqrt_bound(self):
        for v in [F(0),F(1,4),F(2,3),F(1,10**34)]:
            b=sqrt_upper(v)
            self.assertGreaterEqual(b*b,v)
            if b:
                self.assertLess((b-F(1,10**12))**2,v)

    def test_exact_reduces_to_v1(self):
        x,y=F(2,3),F(3,5)
        w=[(x,None),(F(1,2),F(1,2)),(y,None)]
        _,k=word(w)
        state,b=chronology_certificate(*diag(w),k[4][2])
        self.assertEqual(state,"interval")
        self.assertEqual(b["r_interval"],(x**5,x**5))
        self.assertEqual(b["x5_interval"],(x**5,x**5))

    def test_positive_gap_exact_power_grid(self):
        for z in [F(1,3),F(2,3),F(4,5)]:
            for a,d in [(1,2),(2,1),(2,3),(3,2)]:
                for q in [F(1,3),F(1,2)]:
                    for sign in [-1,1]:
                        # Give a rare long-clock cell the same clock as an
                        # ordinary factor; total ordinary-normalized x=z**a.
                        w=[(z,F(1,10**14))]
                        if a>1:
                            w+=[(z**(a-1),None)]
                        # Strict leading population needed: replace the rare
                        # cell clock z by two factors with product z.
                        w[0:1]=[(z+F(1,10),None),(z/(z+F(1,10)),F(1,10**14))]
                        w += [(q,F(1,2)+sign*F(1,10**8)),(z**d,None)]
                        _,k=word(w)
                        status,b=chronology_certificate(*diag(w),k[4][2])
                        self.assertEqual(status,"interval")
                        self.assertGreater(b["gap"],0)
                        lo,hi=b["r_interval"]
                        self.assertLess(hi-lo,F(1,5))
                        p=b["D0"]**(5*a)
                        self.assertLessEqual(lo**(a+d),p)
                        self.assertLessEqual(p,hi**(a+d))
                        lo,hi=b["x5_interval"]
                        self.assertLessEqual(lo,z**(5*a))
                        self.assertLessEqual(z**(5*a),hi)

    def test_positive_gap_separates_reversed_positions(self):
        q,g=F(1,2),F(1,2)+F(1,10**10)
        x,y=F(2,3),F(1,2)
        w1=[(x,None),(q,g),(y,None)]
        w2=[(y,None),(q,g),(x,None)]
        self.assertEqual(diag(w1),diag(w2))
        results=[]
        for w in (w1,w2):
            _,k=word(w)
            status,b=chronology_certificate(*diag(w),k[4][2])
            self.assertEqual(status,"interval")
            results.append(b["r_interval"])
        self.assertLess(results[1][1],results[0][0])

    def test_positive_gap_can_exclude_inconsistent_chronology(self):
        w=[(F(2,3),None),(F(1,2),F(1,2)+F(1,10**8)),(F(3,5),None)]
        self.assertEqual(chronology_certificate(*diag(w),F(0))[0],"excluded")

    def test_zero_gap_boundary_is_strict(self):
        w=[(F(2,3),None),(F(1,2),F(1,2)),(F(3,5),None)]
        _,k=word(w)
        _,b=chronology_certificate(*diag(w),k[4][2])
        self.assertEqual(chronology_certificate(*diag(w),b["baseline"])[0],"excluded")
        self.assertEqual(chronology_certificate(*diag(w),b["baseline"]+b["K"]*(1-b["D0"]**5))[0],
                         "excluded")

if __name__=="__main__":
    unittest.main(verbosity=2)
