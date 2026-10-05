import unittest
import summarize_model_check as s
class Readout(unittest.TestCase):
    def test_inside(self):
        m={k:{'lower':'1/2','upper':'1/2'} for k in s.c.FEATURES};b={k:['1/2','3/4'] for k in m};self.assertEqual(s.mean_status(m,b),'CERTIFIED_INSIDE')
    def test_outside(self):
        m={k:{'lower':'1/2','upper':'2/3'} for k in s.c.FEATURES};b={k:['0','1/3'] for k in m};self.assertEqual(s.mean_status(m,b),'CERTIFIED_OUTSIDE')
    def test_touch_uncertain(self):
        m={k:{'lower':'1/2','upper':'2/3'} for k in s.c.FEATURES};b={k:['0','1/2'] for k in m};self.assertEqual(s.mean_status(m,b),'UNRESOLVED_FINITE_ENCLOSURE')
    def test_common_state(self):
        p=s.truth.TRUTH;f={k:s.F(v) for k,v in p.items()};aux={'A':f['h']+f['u'],'T':f['h']+f['u']+f['v'],'L':f['u']+f['v']};raw={k:{'lower':'1/2','upper':'2/3'} for k in s.c.FEATURES};state={'physical':{k:[v,v] for k,v in p.items()},'aux':{k:[str(v),str(v)] for k,v in aux.items()},'moments':{k:['0','1'] for k in raw}}
        self.assertEqual(s.truth_status([{'state':state}],p,raw),'CERTIFIED_AUGMENTED_CONTAINMENT')
        state['moments']['AC1']=['0','1/2'];self.assertEqual(s.truth_status([{'state':state}],p,raw),'UNRESOLVED_128BIT_MOMENT_CONTAINMENT')
        state['physical']['h']=['0','0'];self.assertEqual(s.truth_status([{'state':state}],p,raw),'PLANTED_PHYSICAL_OR_AUXILIARY_POINT_ABSENT')
if __name__=='__main__':unittest.main()
