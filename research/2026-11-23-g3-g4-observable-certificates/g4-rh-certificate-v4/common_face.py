"""Exact controls for near-ordinary COMMON and the unequal-arm obstruction."""
from fractions import Fraction as F
from math import comb, prod
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/"g4-rh-certificate"))
from certificate import e, mul

def common_step(q0,q1,g):
    A,B=e(q0),e(q1)
    return [[g*x+(1-g)*y for x,y in zip(a,b)] for a,b in zip(A,B)]

def common_word(factors, projected=False):
    K=e(1)
    for q0,q1,g in factors:
        mu=g*q0+(1-g)*q1
        K=mul(K,e(mu) if projected else common_step(q0,q1,g))
    return K

def partial_fraction_second_derivative_bound(n):
    def row(r):
        total=F(0)
        for k in range(1,r+1):
            rates=[comb(i,2) for i in range(k,r+1)]
            num=prod(rates[1:])
            for L in rates:
                den=prod(i-L for i in rates if i!=L)
                total += abs(F(num,den))*L*(L-1)
        return total
    return max((row(r) for r in range(1,n+1)),default=F(0))

def common_proxy_bound(pair,triple,n):
    pair,triple=F(pair),F(triple)
    if not 0 < pair <= 1 or not pair**3 <= triple <= 1 or n<0:
        raise ValueError("outside probability or Jensen bounds")
    J=triple/pair**3-1
    return min(F(1),partial_fraction_second_derivative_bound(n)*J/8)

def tiny_arm_counterexample(N):
    if N<2:
        raise ValueError("strict arms require N>=2")
    z=F(99,100)**2
    g=F(1,4)
    q0,q1=1-F(1,N),1-F(1,10*N)
    mu=g*q0+(1-g)*q1
    i=g*g*q0+(1-g)**2*q1+2*g*(1-g)
    C=z*mu**N
    p2=z*i**N
    c3=z**3*(g*q0**3+(1-g)*q1**3)**N
    return C,p2,c3/pow(C,3)-1,2*p2-1-C

class Tests(unittest.TestCase):
    def test_jensen_identity_and_bound(self):
        fs=[(F(1,2),F(3,5),F(1,4)),(F(1,10),F(4,5),F(7,8))]
        K=common_word(fs)
        terms=[]
        for a,b,g in fs:
            mu=g*a+(1-g)*b
            var=g*(1-g)*(a-b)**2
            eta=(g*a**3+(1-g)*b**3)/mu**3-1
            self.assertEqual(eta,var*(a+b+mu)/mu**3)
            self.assertGreaterEqual(eta,2*var/mu**2)
            terms.append(eta)
        J=K[3][3]/K[2][2]**3-1
        self.assertEqual(1+J,prod(1+t for t in terms))
        self.assertGreaterEqual(J,sum(terms))

    def test_common_proxy_count_kernels(self):
        for a in [F(1,5),F(1,2),F(3,4)]:
            for b in [F(1,4),F(2,5),F(4,5)]:
                for g in [F(1,20),F(1,4),F(1,2),F(19,20)]:
                    fs=[(a,b,g),(F(2,3),F(2,3),F(1,4)),(b,a,g)]
                    K,M=common_word(fs), common_word(fs,True)
                    self.assertEqual(K[2][2],M[2][2])
                    for n in range(1,5):
                        tv=sum(abs(x-y) for x,y in zip(K[n],M[n]))/2
                        self.assertLessEqual(tv,common_proxy_bound(K[2][2],K[3][3],n))

    def test_fixed_gap_with_diminishing_common_defect(self):
        old=None
        for N in [8,16,32,64,128,256,512]:
            C,pi,J,sep=tiny_arm_counterexample(N)
            self.assertGreater(sep,F(1,100))
            self.assertGreaterEqual(pi,(1+C)/2+F(1,200))
            if old is not None:
                self.assertLess(J,old)
            old=J
        self.assertLess(old,F(1,500))

    def test_rational_analytic_limit_separation(self):
        z=F(99,100)**2
        rigorous_lower=2*z*(1-F(19,160))-1-z*(1-F(13,40)+F(13,40)**2/2)
        self.assertEqual(rigorous_lower,F(451111,32000000))
        self.assertGreater(rigorous_lower,0)

if __name__=="__main__":
    unittest.main(verbosity=2)
