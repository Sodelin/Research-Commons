import copy,json,pathlib,subprocess,sys,tempfile,unittest
from unittest.mock import patch
import release_screen as r
class ReleaseTests(unittest.TestCase):
    def test_current_profiles_withhold(self):
        for profile in r.PROFILES:
            out=r.decide(profile);self.assertEqual(out['status'],'WITHHELD_NUMERICAL_RELIABILITY');self.assertIsNone(out['ranked_histories']);self.assertFalse(out['ranking_released']);self.assertFalse(out['fit_or_execution_performed'])
    def test_unknown_profile_not_admitted(self):
        for profile in ['Raubeson','pulse-six-copy','../../input','frog-a01 --approve','']:
            out=r.decide(profile);self.assertEqual(out['status'],'NOT_ADMITTED');self.assertIsNone(out['ranked_histories'])
    def test_changed_pins_fail_closed(self):
        with tempfile.TemporaryDirectory() as d:
            p=pathlib.Path(d);(p/'EVIDENCE-PINS.json').write_text('{}')
            with patch.object(r,'BASE',p):out=r.decide('frog-a01')
            self.assertEqual(out['status'],'EVIDENCE_INVALID');self.assertIsNone(out['ranked_histories'])
    def test_missing_evidence_fail_closed(self):
        with tempfile.TemporaryDirectory() as d:
            with patch.object(r,'ROOT',pathlib.Path(d)):out=r.decide('frog-a01')
        self.assertEqual(out['status'],'EVIDENCE_INVALID')
    def test_prior_controls_not_counted_as_posterior_replicates(self):
        out=r.decide('frog-a01');self.assertEqual(out['diagnostics']['same_budget_long_chains'],2);self.assertEqual(out['diagnostics']['prior_only_controls'],2)
    def test_fixed_tree_not_exposed_as_ranked_history(self):
        out=r.decide('matched-synthetic-a00');self.assertFalse(out['candidate_evidence']['topology_ranking_performed']);self.assertGreater(out['diagnostics']['gap_over_combined_within_chain_heuristic_mcse'],7)
    def test_cli_withheld_nonzero_and_json(self):
        p=subprocess.run([sys.executable,str(r.BASE/'release_screen.py'),'frog-a01'],capture_output=True,text=True);self.assertEqual(p.returncode,2);self.assertIsNone(json.loads(p.stdout)['recommended_history'])
    def test_authenticated_malformed_frog_returns_json(self):
        pins,e=r.read_evidence();e=copy.deepcopy(e);e['frog_diagnostics']['runs']=[None]
        with patch.object(r,'read_evidence',return_value=(pins,e)):out=r.decide('frog-a01')
        self.assertEqual(out['status'],'EVIDENCE_INVALID');self.assertIsNone(out['ranked_histories'])
    def test_authenticated_malformed_matched_returns_json(self):
        pins,e=r.read_evidence();e=copy.deepcopy(e);e['matched_pair']['pair_comparison']['scalars']=None
        with patch.object(r,'read_evidence',return_value=(pins,e)):out=r.decide('matched-synthetic-a00')
        self.assertEqual(out['status'],'EVIDENCE_INVALID');self.assertIsNone(out['ranked_histories'])
    def test_authenticated_wrong_schema_returns_json(self):
        pins,e=r.read_evidence();e=copy.deepcopy(e);e['frog_diagnostics']['schema']='wrong'
        with patch.object(r,'read_evidence',return_value=(pins,e)):out=r.decide('frog-a01')
        self.assertEqual(out['status'],'EVIDENCE_INVALID')
if __name__=='__main__':unittest.main()
