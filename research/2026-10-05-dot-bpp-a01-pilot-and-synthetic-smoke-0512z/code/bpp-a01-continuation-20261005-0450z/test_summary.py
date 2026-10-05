import unittest
import numpy as np
from summarize_a01 import parse,ess,tv,dist
class SummaryTests(unittest.TestCase):
    def test_order_and_attributes(self):
        a=parse('((K #.001: .01,C #.002:.01) #.003:.02,(H #.004:.02,L #.005:.02)#.006:.01)#.007;')
        b=parse('((L:.02,H:.02):.01,(C:.01,K:.01):.02);')
        self.assertEqual(a,b);self.assertEqual(a[0],'((C,K),(H,L));');self.assertEqual(a[1],frozenset(['CK','HL']));self.assertAlmostEqual(a[2],.03)
    def test_root_preserved(self):
        a=parse('(((K,C),H),L);')[0];b=parse('((K,C),(H,L));')[0];self.assertNotEqual(a,b)
    def test_bad_inputs(self):
        for s in ['((K,C),(H,H));','((K,C),(H,X));','(K,C,H,L);','((K,C),(H,L)); rubbish','((K:-1,C),(H,L));','((K:.2,C:.1),(H,L));']:
            with self.assertRaises((ValueError,IndexError)):parse(s)
    def test_constant_no_ess(self):
        self.assertIsNone(ess([0.]*100)['ess']);self.assertIsNone(ess([1.]*100)['mcse'])
    def test_ess_iid_and_blocked(self):
        rng=np.random.default_rng(17);iid=rng.integers(0,2,10000);blocked=np.repeat(rng.integers(0,2,100),100)
        self.assertGreater(ess(iid)['ess'],2000);self.assertLess(ess(blocked)['ess'],300)
    def test_tv(self):
        self.assertEqual(tv(dist(['a','b']),dist(['a','b'])),0);self.assertEqual(tv({'a':1},{'b':1}),1)
if __name__=='__main__':unittest.main()
