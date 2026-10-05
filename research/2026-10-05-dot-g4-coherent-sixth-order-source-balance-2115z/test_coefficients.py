import unittest
from fractions import Fraction as F
import source_coefficients as s
class Small(unittest.TestCase):
    def test_split_forget(self):
        states,ids,q,r=s.m.build(4);cs,ci,ql,qr=s.coloured(4)
        for i in range(len(states)):
            v=[F(0)]*len(states);v[i]=F(1);w=s.split(v,states,ci);back=[F(0)]*len(states)
            for value,(a,b) in zip(w,cs):back[ids[tuple(sorted(a+b))]]+=value
            self.assertEqual(back,v)
    def test_arm_commutation(self):
        cs,ci,l,r=s.coloured(3)
        for i in range(len(cs)):
            v=[F(0)]*len(cs);v[i]=F(1);self.assertEqual(s.m.apply(s.m.apply(v,l),r),s.m.apply(s.m.apply(v,r),l))
    def test_expansion(self):
        self.assertEqual(s.expansion({(1,0):F(1),(0,1):F(1)},3),{(1,1,0):F(-2)})
        self.assertEqual(s.expansion({(1,1):F(1)},3),{(2,2,0):F(1),(3,0,1):F(-1)})
    def test_binomial(self):
        q=[{0:F(-1),1:F(1)},{}];v=[F(1),F(0)]
        one=s.binomial_next(v,q,0);self.assertEqual(one,[F(1),F(-1)]);self.assertEqual(s.binomial_next(one,q,1),[0,0])
if __name__=='__main__':unittest.main()
