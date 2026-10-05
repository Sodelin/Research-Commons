import unittest
import summarize_completed_pair as s
class PairTests(unittest.TestCase):
    def test_fixed_truth_interval_facts(self):
        truth={k:{'theta':2.} for k in ['K','C','L','H']};truth['C,H,K,L']={'tau':2.}
        keys=['theta_K','theta_C','theta_L','theta_H','root_tau']
        reports=[{'scalars':{'columns':{k:{'quantiles_025_50_975':q} for k in keys}}} for q in [[1.,1.5,2.],[2.1,3.,4.]]]
        result=s.truth_facts(reports,truth)
        for value in result.values():self.assertEqual(value['truth_in_interval'],[True,False]);self.assertEqual(value['declared_fixed_truth'],2.)
    def test_missing_truth_rejected(self):
        with self.assertRaises(KeyError):s.truth_facts([], {})
    def test_changed_helper_rejected(self):
        with self.assertRaisesRegex(ValueError,'changed reviewed helper'):s.load('compare_matched','incorrect')
if __name__=='__main__':unittest.main()
