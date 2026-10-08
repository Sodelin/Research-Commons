import unittest
from fractions import Fraction as F
import certified_forward as f
from verify_controls import ExpPoly,integrate_pieces,FIXTURES

def positive_taylor_oracle(x,n=160):
    x=F(x);term=F(1);s=F(1)
    for j in range(1,n+1):term*=x/j;s+=term
    next_term=term*x/(n+1)
    if n+2<2*x:raise ValueError
    return f.Interval(1/(s+2*next_term),1/s)

class ForwardTests(unittest.TestCase):
    def test_interval_operations_and_rounding(self):
        a=f.Interval(F(1,3),F(1,2));b=f.Interval(-2,-1)
        self.assertEqual((a*b),f.Interval(-1,F(-1,3)));self.assertTrue((1-a).contains(F(3,5)))
        d=a.dyadic(20);self.assertLessEqual(d.lo,a.lo);self.assertGreaterEqual(d.hi,a.hi)
    def test_exp_against_independent_positive_series(self):
        for x in [F(1,64),F(1),F(37,8),F(55,2)]:
            a=f.exp_neg(x,64);b=positive_taylor_oracle(x)
            self.assertLessEqual(a.lo,b.lo);self.assertGreaterEqual(a.hi,b.hi);self.assertLessEqual(a.width,F(1,1<<64))
    def test_exp_zero_and_large_argument(self):
        self.assertEqual(f.exp_neg(F(0),64),f.Interval.point(1));self.assertEqual(f.exp_neg(F(1000),64),f.Interval(0,F(1,1<<64)))
    def test_domain_rejections(self):
        p=dict(FIXTURES['distinct_rates'])
        for key,value in [('h',0),('t1','1/16'),('g',1),('rA',0),('rB',1.25)]:
            q=dict(p);q[key]=value
            with self.assertRaises(f.DomainError):f.validate(q)
        q=dict(p);q['extra']=1
        with self.assertRaises(f.DomainError):f.validate(q)
        with self.assertRaises(f.ResourceBound):f.rational(1<<300)
        with self.assertRaises(f.ResourceBound):f.rational('0'*200+'1')
    def test_symbolic_density_normalizations(self):
        for p in FIXTURES.values():
            p=f.validate(p)
            for m in integrate_pieces(p,F(0)).values():self.assertEqual(m.terms,{F(0):F(1)})
    def test_separate_formula_and_piecewise_forms(self):
        for p in FIXTURES.values():
            p=f.validate(p)
            for z in [F(0),F(8,3),F(16,3),F(440,3)]:
                a=f.pair_expressions(p,z,ExpPoly.E);b=integrate_pieces(p,z)
                for pair in f.PAIRS:self.assertEqual(a[pair].terms,b[pair].terms)
    def test_primitive_rejects_float_bool_even_after_cache(self):
        f.exp_neg(F(0),64)
        for x in [0.0,False]:
            with self.assertRaises(f.DomainError):f.exp_neg(x,64)
        with self.assertRaises(f.DomainError):f.pair_expressions(f.validate(FIXTURES['equal_rates']),0.0,ExpPoly.E)
    def test_one_argument_interval_forward(self):
        p=f.validate(FIXTURES['distinct_rates']);m=f.pair_expressions(p,F(8,3),lambda x:f.exp_neg(x,80));exact=integrate_pieces(p,F(8,3))
        for pair in f.PAIRS:
            self.assertTrue(m[pair].intersects(exact[pair].enclosed(90)));mean=(1+m[pair])/2
            self.assertGreaterEqual(mean.lo,F(1,2));self.assertLessEqual(mean.hi,F(1))
if __name__=='__main__':unittest.main()
