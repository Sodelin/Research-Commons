"""Mock/source-binding tests only; no generated-sample inference or truth evaluation."""
import copy,json,unittest
from pathlib import Path
from unittest.mock import patch
import integration_core as c
import compose_run as r
import prepare_model_request as p
from test_admission_composition import report_fixture
BASE=Path(__file__).resolve().parent
class Tests(unittest.TestCase):
    def admission(self):
        manifest=json.loads((BASE/'declared-model/CONTROL-MANIFEST.json').read_text());req,_=c.request(BASE/'declared-model/REQUEST.json',manifest['request_sha256']);return manifest,req
    def test_model_record_is_qualified_and_bound(self):
        manifest,req=self.admission();a=c.admission(BASE/'declared-model/ADMISSION.json',BASE/'ADMISSION-REGISTRY.json',c.TRUSTED_REGISTRY_SHA,req);self.assertEqual(a['classification'],'synthetic_model_check');self.assertTrue(all(value=='ideal_model_semantics_reviewed_finite_rng_not_certified' for value in a['premises'].values()));self.assertEqual(a['generation_receipt_sha256'],c.GENERATION_RECEIPT_SHA)
    def test_mismatched_generation_qualification_is_refused(self):
        manifest,req=self.admission();real=c.read
        def changed(path,expected):
            d=real(path,expected)
            if Path(path).name=='GENERATION-RECEIPT.json':d['iid_randomness_certified']=True
            return d
        with patch.object(c,'read',side_effect=changed):
            with self.assertRaises(c.NotAdmitted):c.admission(BASE/'declared-model/ADMISSION.json',BASE/'ADMISSION-REGISTRY.json',c.TRUSTED_REGISTRY_SHA,req)
    def test_synthetic_report_never_eligible_for_data_confidence(self):
        args=list(report_fixture());args[0]['admission_classification']='synthetic_model_check';args[0]['scientific_premises']={f'A{i}':'ideal_model_semantics_reviewed_finite_rng_not_certified' for i in range(1,7)};args[0]['generation_receipt_sha256']=c.GENERATION_RECEIPT_SHA;args[0]['generation_review_sha256']=c.GENERATION_REVIEW_SHA
        out=r.report(*args);self.assertTrue(out['status'].startswith('SYNTHETIC_MODEL_CHECK_'));self.assertFalse(out['data_confidence_certificate_eligible']);self.assertFalse(out['data_confidence_certificate_issued']);self.assertFalse(out['finite_generator_law_certified']);self.assertEqual(out['confidence_error_bound_scope'],'conditional_ideal_model_only')
    def test_requested_domain_and_budget_not_truth_neighborhood(self):
        manifest,req=self.admission();prior=c.read(c.PROVIDER/'declared-requests/distinct.json','a73fc025632555e058b8dc6f2c1440e6f625409caefd36ae56b660f0ba79cedb');self.assertEqual(req['domain'],prior['box']);self.assertEqual(req['normalized_width_targets'],prior['normalized_width_targets']);self.assertEqual(req['inverse_budget']['max_splits'],0);self.assertEqual(req['inverse_budget']['max_stages'],16);self.assertEqual(req['delta'],'1/10');self.assertEqual(req['expected_loci'],1024)
if __name__=='__main__':unittest.main()

class TruthReportAPI(unittest.TestCase):
    def test_json_report_api(self):
        import evaluate_truth as t
        from types import SimpleNamespace
        from unittest.mock import patch,Mock
        expected={'schema':'fixed-pulse-certified-forward-v1','parameters':{'h':'1/16'},'features':{'AC':[{'k':1,'mean_interval':{'lower':'1/2','upper':'3/4'},'laplace_interval':{'lower':'0','upper':'1/2'}}]}}
        report=Mock(return_value=expected)
        provider=SimpleNamespace(m=SimpleNamespace(forward=SimpleNamespace(report=report)))
        with patch.object(t.c,'read',return_value={'physical_truth':t.TRUTH}),patch.object(t.c,'load_provider',return_value=provider):
            result=t.evaluate();encoded=t.c.canonical(result)
            self.assertEqual(json.loads(encoded)['forward'],expected)
            self.assertEqual(json.loads(encoded)['physical_truth'],t.TRUTH)
        self.assertEqual(report.call_count,1);self.assertEqual(report.call_args.args[1],128)
        self.assertFalse(result['observed_data_read'])
