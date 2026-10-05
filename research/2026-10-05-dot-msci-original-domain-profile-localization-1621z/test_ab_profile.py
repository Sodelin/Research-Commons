"""Tiny exact-arithmetic and mocked profile preservation controls."""
import unittest
from fractions import Fraction as F
from unittest.mock import patch
import global_contractors as o
import interval_math as m
from test_journal import setup
import tempfile
import global_engine as e
I=m.I
class Tests(unittest.TestCase):
    def test_hypothetical_rate_can_exceed_physical_prior(self):
        A=F(1,8);T=I.point(F(3,16));R=I.point(5);physical_rate=I(F(39,10),F(41,10))
        v1=o.rectangle_two_stage(o.Z,I.point(A),I.point(4),T,R)
        enclosure,detail=o.profile_enclosure(F(5,32),T,R,v1)
        final=list(map(F,detail['final_hypothetical_rate']))
        self.assertGreater(final[0],physical_rate.hi);self.assertFalse(detail['physical_rate_prior_intersected']);self.assertLess(enclosure.lo,enclosure.hi)
    def test_uncertain_root_box_encloses_known_profile_tuple(self):
        A=F(1,8);T0=F(3,16);R0=F(5);r=F(4);eps=F(1,4096)
        exact1=o.rectangle_two_stage(o.Z,I.point(A),I.point(r),I.point(T0),I.point(R0));exact2=o.rectangle_two_stage(2*o.Z,I.point(A),I.point(r),I.point(T0),I.point(R0))
        result,detail=o.profile_enclosure(A,I(T0-eps,T0+eps),I(R0-eps,R0+eps),I(exact1.lo-eps,exact1.hi+eps))
        self.assertLessEqual(result.lo,exact2.lo);self.assertGreaterEqual(result.hi,exact2.hi);lo,hi=map(F,detail['final_hypothetical_rate']);self.assertLessEqual(lo,r);self.assertGreaterEqual(hi,r)
    def test_equal_rates_have_no_singular_formula(self):
        A=F(1,8);T=I.point(F(3,16));R=I.point(4)
        first=o.rectangle_two_stage(o.Z,I.point(A),R,T,R);second=o.rectangle_two_stage(2*o.Z,I.point(A),R,T,R);value,detail=o.profile_enclosure(A,T,R,first)
        self.assertLessEqual(value.lo,second.lo);self.assertGreaterEqual(value.hi,second.hi)
    def test_failed_uniform_guards_refuse_comparison(self):
        T=I(F(1,8),F(3,16));R=I(1,5)
        for trial,V1 in [(F(1,8),I(F(1,3),F(1,2))),(F(0),I(0,1))]:
            with self.assertRaises(o.GuardUnavailable):o.profile_enclosure(trial,T,R,V1)
    def test_touching_second_moment_does_not_cut(self):
        state={'aux':{'A':I(F(1,4),F(3,4))}};log=[];target=I(F(1,3),F(2,3))
        o.scalar_bracket(state,'aux','A',target,lambda _:I(F(2,3),F(3,4)),False,2,log);self.assertEqual(state['aux']['A'],I(F(1,4),F(3,4)))
    def test_hypothetical_rate_not_written_to_actual_state(self):
        with tempfile.TemporaryDirectory() as td:
            _,_,q=setup(td);state=e.initial_cell(q)['state'];before=state['physical']['rAB'];value=I(0,1)
            with patch.object(o,'profile_enclosure',return_value=(value,{'mock':'no cut'})):o.AB_profile_stage(state,[],outer_steps=1)
            self.assertEqual(state['physical']['rAB'],before)
    def test_unsupported_profile_discards_complete_pre_state(self):
        with tempfile.TemporaryDirectory() as td:
            _,_,q=setup(td);state=e.initial_cell(q)['state'];before=o.record(state)
            with patch.object(o,'profile_enclosure',side_effect=m.Unsupported('tiny declared refusal')):
                with self.assertRaises(m.Unsupported):o.operate(state,'AB',1)
            self.assertEqual(o.record(state),before)
    def test_both_strict_profile_slab_directions(self):
        A=F(1,8);T=I.point(F(3,16));R=I.point(5);rate=I.point(4)
        first=o.rectangle_two_stage(o.Z,I.point(A),rate,T,R);second=o.rectangle_two_stage(2*o.Z,I.point(A),rate,T,R)
        left,_=o.profile_enclosure(A-F(1,64),T,R,first);right,_=o.profile_enclosure(A+F(1,64),T,R,first)
        self.assertGreater(left.lo,second.hi);self.assertLess(right.hi,second.lo)
    def test_separate_finite_step_caps(self):
        with self.assertRaises(ValueError):o.profile_enclosure(F(0),I.point(1),I.point(1),I(F(1,3),F(1,2)),17)
        with self.assertRaises(ValueError):o.AB_profile_stage({},[],outer_steps=9)
if __name__=='__main__':unittest.main()
