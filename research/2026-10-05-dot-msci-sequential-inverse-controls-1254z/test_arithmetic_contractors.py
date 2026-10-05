import hashlib,json,unittest
from fractions import Fraction as F
from pathlib import Path
from unittest.mock import patch
import interval_math as m
import contractors as c
I=m.I
FIXTURE=Path(__file__).resolve().parent.parent/'msci-330-feature-public-20261005-1039z/evaluator/CONTROL-RESULTS.json'
FIXTURE_SHA='acf3a3cfe6addaa79a29106c3aca9985e5247b18e4c31b41a50ff0d9e8552c6a'
def point_state(name='distinct_rates'):
    raw=FIXTURE.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=FIXTURE_SHA:raise ValueError('fixture pin')
    ref=json.loads(raw)['fixtures'][name];p={k:F(v) for k,v in ref['parameters'].items()}
    values=dict(h=p['h'],u=p['t1']-p['h'],v=p['t0']-p['t1'],**{k:p[k] for k in ('rA','rB','rC','rAB','rR','g')})
    obs={key:I(0,1) for key in m.FEATURES}
    return c.initial({k:I.point(v) for k,v in values.items()},obs),p
class Tests(unittest.TestCase):
    def test_point_pair_formula_inclusions_both_published_fixtures(self):
        for name in ('distinct_rates','equal_rates'):
            state,p=point_state(name);actual=m.selected(state['physical'],state['aux']);_,reference,_=m.forward.evaluate(p,96)
            for key,interval in actual.items():
                expected=reference[key[:-1]][int(key[-1])-1]
                self.assertLessEqual(interval.lo,expected.lo);self.assertGreaterEqual(interval.hi,expected.hi)
    def test_exp_and_primitive_endpoint_guards(self):
        self.assertEqual(m.S(I(1,2),I.point(0)),I.point(1));self.assertEqual(m.H(F(8,3),I(1,2),I.point(0)),I.point(0))
        with self.assertRaises(m.Unsupported):m.S(I(0,1),I(1,2))
        with self.assertRaises(m.Unsupported):m.divide(I(1,2),I(-1,1))
        with self.assertRaises(m.Unsupported):m.E(I(-1,1))
    def test_endpoint_touch_retained(self):self.assertEqual(m.meet(I(0,F(1,2)),I(F(1,2),1)),I.point(F(1,2)))
    def test_linear_projection_is_exact_and_contracting(self):
        state,_=point_state();state['physical']['h']=I(F(1,32),F(3,32));state['aux']['A']=I.point(F(1,8));out,_=c.operate(state,'linear');self.assertEqual(out['physical']['h'],I.point(F(1,16)))
    def test_root_zero_denominator_guard_is_skipped(self):
        state,_=point_state();out,log=c.operate(state,'root_q');self.assertEqual(log['ratio_guard'],'SKIPPED_ZERO_DENOMINATOR');self.assertEqual(c.record(out),c.record(state))
    def test_trial_rate_uses_whole_nuisance_and_tied_rate(self):
        state,_=point_state();state['physical']['rB']=I(1,5);seen=[]
        def fake(p,a,z):seen.append((dict(p),dict(a)));return {pair:I(0,1) for pair in ('AA','BB','CC','AB','BC','AC')}
        with patch.object(m,'pair_intervals',side_effect=fake):out,log=c.operate(state,'rate_B')
        self.assertEqual(seen[0][0]['rB'],I.point(3));self.assertEqual(seen[0][1],state['aux']);self.assertEqual(c.record(out),c.record(state))
    def test_strict_rate_slab_cut_only(self):
        state,_=point_state();state['physical']['rC']=I(1,5);state['moments']['CC1']=I(F(1,2),F(3,4))
        with patch.object(m,'pair_intervals',return_value={'CC':I(0,F(1,2))}):out,_=c.operate(state,'rate_C');self.assertEqual(out['physical']['rC'],I(1,5))
        with patch.object(m,'pair_intervals',return_value={'CC':I(0,F(1,3))}):out,_=c.operate(state,'rate_C');self.assertEqual(out['physical']['rC'],I(3,5))
    def test_unknown_operator_refused(self):
        state,_=point_state()
        with self.assertRaises(ValueError):c.operate(state,'AB_exact_curve')
if __name__=='__main__':unittest.main()
