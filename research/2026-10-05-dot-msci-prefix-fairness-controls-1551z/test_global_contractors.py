"""Small primitive/monotonicity tests; no complete original-domain trial."""
import unittest
from fractions import Fraction as F
import interval_math as m
import global_contractors as g
I=m.I
class Tests(unittest.TestCase):
    def test_increasing_interval_target_bracket(self):
        state={'physical':{'r':I(0,1)}};logs=[];g.scalar_bracket(state,'physical','r',I(F(1,3),F(2,3)),lambda r:I.point(r),True,12,logs);out=state['physical']['r']
        self.assertTrue(out.contains(F(1,3)));self.assertTrue(out.contains(F(2,3)));self.assertLess(out.width,F(1,3)+F(1,1024))
    def test_decreasing_interval_target_bracket(self):
        state={'aux':{'T':I(0,1)}};g.scalar_bracket(state,'aux','T',I(F(1,3),F(2,3)),lambda t:I.point(1-t),False,12,[]);out=state['aux']['T'];self.assertTrue(out.contains(F(1,3)));self.assertTrue(out.contains(F(2,3)))
    def test_guard_refusal_keeps_range(self):
        state={'aux':{'A':I(0,1)}}
        def refuse(_):raise g.GuardUnavailable('mock trial guard')
        g.scalar_bracket(state,'aux','A',I(F(1,3),F(2,3)),refuse,False,4,[]);self.assertEqual(state['aux']['A'],I(0,1))
    def test_closed_contact_survives(self):
        state={'physical':{'r':I(F(1,4),F(3,4))}};g.scalar_bracket(state,'physical','r',I(0,F(1,4)),lambda r:I.point(r),True,8,[]);self.assertTrue(state['physical']['r'].contains(F(1,4)))
    def test_endpoint_can_certify_inconsistency(self):
        state={'physical':{'r':I(F(1,4),F(3,4))}};log=[]
        with self.assertRaises(m.Inconsistent):g.scalar_bracket(state,'physical','r',I(0,F(1,8)),lambda r:I.point(r),True,8,log)
        self.assertEqual(len(log),1)
    def test_equal_rate_CC_is_independent_of_root_time(self):
        out=g.rectangle_two_stage(g.Z,I.point(0),I.point(2),I(F(1,10),F(3,10)),I.point(2));self.assertTrue(out.contains(F(3,7)));self.assertLessEqual(out.width,F(1,2**79))
    def test_corner_guard_and_positive_length_fallback(self):
        onset=I(F(1,8),F(1,4));T=I(F(3,16),F(3,10));rate=I(2,3);root=I(4,5)
        with self.assertRaises(g.GuardUnavailable):g.rectangle_two_stage(g.Z,onset,rate,T,root)
        result,kind=g.actual_two_stage(g.Z,onset,rate,I(F(1,32),F(1,8)),T,root);self.assertEqual(kind,'positive_physical_length_fallback');self.assertGreaterEqual(result.hi,result.lo)
    def test_general_corner_encloses_interior_two_stage_value(self):
        out=g.rectangle_two_stage(g.Z,I(F(1,16),F(1,8)),I(2,4),I(F(3,16),F(1,4)),I(3,5))
        point=g.point_two_stage(g.Z,F(3,32),F(3),F(7,32),F(4));self.assertLessEqual(out.lo,point.lo);self.assertGreaterEqual(out.hi,point.hi)
    def test_positive_signal_bound(self):
        D,B,details=g.positive_D(g.Z,I.point(F(1,16)),I.point(3),I.point(F(1,8)),I.point(F(3,16)),I.point(5));self.assertGreater(D.lo,0);self.assertGreater(F(details['positive_lower']),0)
    def test_underresolved_positive_signal_does_not_invent_epsilon(self):
        D,B,details=g.positive_D(g.Z,I.point(F(1,8)),I.point(F(1,2**200)),I.point(F(1,2**100)),I.point(F(1,8)+F(1,2**100)),I.point(2));self.assertEqual(F(details['positive_lower']),0);self.assertEqual(D.lo,0)
if __name__=='__main__':unittest.main()
