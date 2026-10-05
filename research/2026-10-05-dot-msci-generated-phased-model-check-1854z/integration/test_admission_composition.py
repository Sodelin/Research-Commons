import copy,json,tempfile,unittest
from pathlib import Path
from fractions import Fraction as F
from unittest.mock import patch
import integration_core as c
import compose_run as r
import prepare_input as p
BASE=Path(__file__).resolve().parent

def declared(name='literal_two'):
    manifest=json.loads((BASE/'declared-protocols/CONTROL-MANIFEST.json').read_text());entry=next(x for x in manifest['controls'] if x['name']==name);folder=BASE/'declared-protocols';req,_=c.request(folder/entry['request'],entry['request_sha256']);return folder,entry,req

def report_fixture(empty=False,mode='normal_validated'):
    provider=c.load_provider();import global_check as check
    folder,entry,req=declared();inv={'schema':provider.SCHEMA,'model':c.MODEL,'quantity':'shifted_bernoulli_character_mean','box':req['domain'],'features':{key:['0','1'] for key in c.FEATURES},'normalized_width_targets':req['normalized_width_targets'],'budget':req['inverse_budget'],'provenance':{'kind':'mock report only'}}
    with tempfile.TemporaryDirectory() as td:
        path=Path(td)/'q';path.write_bytes(c.canonical(inv));identity=c.sha(path.read_bytes());parsed=provider.read_request(path,identity)
    frontier={} if empty else {'r':provider.initial_cell(parsed)}
    output=check.output(parsed,frontier,mode,{'complete_numeric_replay':mode=='normal_validated','resource_limited':mode!='normal_validated'})
    preparation={'admission_classification':'protocol_fixture','inverse_request_sha256':identity,'scientific_premises':{f'A{i}':'not_asserted_protocol_fixture' for i in range(1,7)},'dataset_sha256':entry['dataset_sha256'],'admission_sha256':entry['admission_sha256'],'analysis_request_sha256':entry['request_sha256'],'trusted_registry_sha256':c.TRUSTED_REGISTRY_SHA,'extraction_sha256':'1'*64,'confidence_sha256':'2'*64}
    confidence={'delta':'1/10','mode':'FULL_RANGE_CERTIFIED','error_upper_bound':'0'}
    return preparation,confidence,output,parsed,provider
class Tests(unittest.TestCase):
    def test_registry_is_source_anchored(self):
        folder,entry,req=declared();a=c.admission(folder/entry['admission'],BASE/'ADMISSION-REGISTRY.json',c.TRUSTED_REGISTRY_SHA,req);self.assertEqual(a['classification'],'protocol_fixture')
        with self.assertRaises(c.NotAdmitted):c.admission(folder/entry['admission'],BASE/'ADMISSION-REGISTRY.json','0'*64,req)
    def test_self_rehashed_registry_not_admitted(self):
        folder,entry,req=declared();d=json.loads((BASE/'ADMISSION-REGISTRY.json').read_text());d['admissions'][entry['admission_sha256']]['classification']='scientifically_admitted'
        with tempfile.TemporaryDirectory() as td:
            path=Path(td)/'registry';path.write_bytes(c.canonical(d))
            with self.assertRaises(c.NotAdmitted):c.admission(folder/entry['admission'],path,c.sha(path.read_bytes()),req)
    def test_unregistered_and_changed_analysis_refused(self):
        folder,entry,req=declared('unregistered')
        with self.assertRaises(c.NotAdmitted):c.admission(folder/entry['admission'],BASE/'ADMISSION-REGISTRY.json',c.TRUSTED_REGISTRY_SHA,req)
        folder,entry,req=declared();req['delta']='1/100'
        with self.assertRaises(c.NotAdmitted):c.admission(folder/entry['admission'],BASE/'ADMISSION-REGISTRY.json',c.TRUSTED_REGISTRY_SHA,req)
    def test_protocol_output_never_issues_data_confidence(self):
        out=r.report(*report_fixture());self.assertTrue(out['status'].startswith('PROTOCOL_ONLY_'));self.assertFalse(out['data_confidence_certificate_issued']);self.assertIsNone(out['false_issued_certificate_error_bound']);self.assertFalse(out['coverage_conditional_on_success_claimed'])
    def test_checked_empty_is_conditional_incompatibility(self):
        out=r.report(*report_fixture(empty=True));self.assertEqual(out['status'],'PROTOCOL_ONLY_CONDITIONAL_INCOMPATIBILITY');self.assertFalse(out['whole_union_width_target_met']);self.assertFalse(out['nonempty_cover'])
    def test_prefix_is_unknown_and_not_complete(self):
        out=r.report(*report_fixture(mode='recovered_same_process_validated_prefix'));self.assertIn('UNKNOWN',out['status']);self.assertFalse(out['complete_numeric_replay']);self.assertFalse(out['whole_union_width_target_met'])
    def test_bad_replay_or_identity_is_refused(self):
        for mutate in [lambda x:x.update(mode='recovered_authenticated_original_domain'),lambda x:x.update(request_sha256='0'*64),lambda x:x['details'].update(complete_numeric_replay=False)]:
            args=list(report_fixture());mutate(args[2])
            with self.assertRaises(ValueError):r.report(*args)
    def test_tampered_width_is_refused(self):
        args=list(report_fixture());args[2]['widths']['h']['width']='0'
        with self.assertRaises(ValueError):r.report(*args)
    def test_late_extraction_failure_never_calls_confidence(self):
        folder,entry,req=declared()
        with tempfile.TemporaryDirectory() as td,patch.object(c,'extract',side_effect=c.InputResource('mock partial stream stop')),patch.object(c,'confidence') as conf:
            result=p.prepare(folder/entry['request'],entry['request_sha256'],folder/entry['dataset'],folder/entry['admission'],BASE/'ADMISSION-REGISTRY.json',c.TRUSTED_REGISTRY_SHA,Path(td)/'out');conf.assert_not_called();self.assertEqual(result['status'],'INPUT_RESOURCE_LIMIT');self.assertIsNone(result['confidence_sha256']);self.assertFalse((Path(td)/'out/EXTRACTION.json').exists())
    def test_initial_copy_failure_retains_terminal(self):
        folder,entry,req=declared();pins={'sources':{},'admission_registry_sha256':c.TRUSTED_REGISTRY_SHA}
        with tempfile.TemporaryDirectory() as td,patch.object(r,'authenticate',return_value=pins),patch.object(r,'copy_input',side_effect=OSError('tiny mock failure')):
            result=r.run(folder/entry['request'],entry['request_sha256'],folder/entry['dataset'],folder/entry['admission'],Path(td)/'attempt','unused','0'*64);self.assertEqual(result['error']['type'],'OSError');self.assertFalse(result['data_confidence_certificate_issued']);self.assertTrue((Path(td)/'attempt/TERMINAL.json').exists())
if __name__=='__main__':unittest.main()

class TerminalAuthorityTests(unittest.TestCase):
    def test_candidate_report_cannot_issue_before_terminal_inventory(self):
        args=list(report_fixture());args[0]['admission_classification']='scientifically_admitted';args[0]['scientific_premises']={f'A{i}':'assumed_under_independent_scientific_review' for i in range(1,7)}
        out=r.report(*args);self.assertTrue(out['data_confidence_certificate_eligible']);self.assertFalse(out['data_confidence_certificate_issued']);self.assertTrue(out['requires_successful_terminal_inventory'])

class ExecutionFailureTests(unittest.TestCase):
    def inputs(self):
        folder,entry,req=declared();pins={'sources':{},'admission_registry_sha256':c.TRUSTED_REGISTRY_SHA};return folder,entry,pins
    def test_abrupt_preparation_cannot_release_partial_stdout(self):
        folder,entry,pins=self.inputs();c.load_provider();import bounded_runner as runner
        def stopped(command,attempt,label,watchdog,wall):
            (attempt/(label+'.stdout')).write_text('{"status":"COMPLETE_ADMITTED_PREPARATION"}')
            return {'status':'RESOURCE_TIME_LIMIT','exit_code':-15}
        with tempfile.TemporaryDirectory() as td,patch.object(r,'authenticate',return_value=pins),patch.object(runner,'stage',side_effect=stopped):
            out=r.run(folder/entry['request'],entry['request_sha256'],folder/entry['dataset'],folder/entry['admission'],Path(td)/'attempt','unused','0'*64);self.assertFalse(out['fresh_inverse_executed']);self.assertFalse(out['data_confidence_certificate_issued']);self.assertIsNotNone(out['error'])
    def test_composed_write_failure_has_terminal_failure_receipt(self):
        folder,entry,pins=self.inputs();real=r.write_new
        def failure(path,value):
            if Path(path).name=='COMPOSED-RESULT.json':raise OSError('mock result write failure')
            return real(path,value)
        with tempfile.TemporaryDirectory() as td,patch.object(r,'authenticate',return_value=pins),patch.object(r,'copy_input',side_effect=OSError('initial mock stop')),patch.object(r,'write_new',side_effect=failure):
            out=r.run(folder/entry['request'],entry['request_sha256'],folder/entry['dataset'],folder/entry['admission'],Path(td)/'attempt','unused','0'*64);self.assertIsNotNone(out['output_failure']);self.assertIsNone(out['composed_output_sha256']);self.assertFalse(out['data_confidence_certificate_issued'])
    def test_inventory_failure_prevents_terminal_acceptance(self):
        folder,entry,pins=self.inputs();c.load_provider();import bounded_runner as runner
        class Bad:
            def tree_bytes(self,*_):raise OSError('mock inventory failure')
        with tempfile.TemporaryDirectory() as td,patch.object(r,'authenticate',return_value=pins),patch.object(r,'copy_input',side_effect=OSError('initial mock stop')),patch.object(runner,'load_watchdog',return_value=Bad()):
            out=r.run(folder/entry['request'],entry['request_sha256'],folder/entry['dataset'],folder/entry['admission'],Path(td)/'attempt','unused','0'*64);self.assertIsNotNone(out['inventory_failure']);self.assertFalse(out['data_confidence_certificate_issued'])
