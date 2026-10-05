import unittest
from fractions import Fraction as F
import summarize_results as s
import seq_engine as e
import joint_contractor as ops
import interval_math as m
from test_state_recovery import request_dict
class Tests(unittest.TestCase):
    def test_augmented_containment_includes_all_intervals(self):
        physical={key:['1','2'] for key in ops.PHYSICAL};physical['g']=['1/4','3/4'];point={key:'3/2' for key in ops.PHYSICAL};point['g']='1/2'
        state={'physical':physical,'aux':{'A':['2','4'],'T':['3','6'],'L':['2','4']},'moments':{key:['0','1'] for key in m.FEATURES}}
        raw={key:{'lower':'1/4','upper':'3/4'} for key in m.FEATURES}
        self.assertEqual(s.truth_status([{'state':state}],point,raw),'CERTIFIED_AUGMENTED_CONTAINMENT')
        state['moments']['AC1']=['1/3','2/3']
        self.assertEqual(s.truth_status([{'state':state}],point,raw),'UNRESOLVED_128BIT_MOMENT_CONTAINMENT')
        state['physical']['h']=['1','5/4']
        self.assertEqual(s.truth_status([{'state':state}],point,raw),'PLANTED_PHYSICAL_OR_AUXILIARY_POINT_ABSENT')
    def test_one_bad_state_does_not_hide_another_valid_state(self):
        state={'physical':{key:['0','3'] for key in ops.PHYSICAL},'aux':{'A':['0','6'],'T':['0','9'],'L':['0','6']},'moments':{key:['0','1'] for key in m.FEATURES}}
        point={key:'1' for key in ops.PHYSICAL};raw={key:{'lower':'1/4','upper':'3/4'} for key in m.FEATURES}
        bad={group:dict(values) for group,values in state.items()};bad['physical']['h']=['2','3']
        self.assertEqual(s.truth_status([{'state':bad},{'state':state}],point,raw),'CERTIFIED_AUGMENTED_CONTAINMENT')
if __name__=='__main__':unittest.main()
