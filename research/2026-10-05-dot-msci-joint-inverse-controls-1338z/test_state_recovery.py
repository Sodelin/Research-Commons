"""Geometry/recovery tests use an explicitly mocked identity function, not MSci trials."""
import tempfile,time,unittest
from pathlib import Path
from unittest.mock import patch
import seq_engine as e
import seq_check as v
import joint_contractor as j
import interval_ad as ad
import interval_math as m
from test_ad_joint import identity_ad

def request_dict(**budget):
    limits=dict(max_operations=0,max_splits=0,max_depth=2,sweeps_per_cell=1,wall_ms=1000,recovery_wall_ms=1000,recovery_max_operations=16,preconditioner='auto');limits.update(budget)
    return {'schema':e.SCHEMA,'model':e.MODEL,'quantity':'shifted_bernoulli_character_mean','box':{key:['1/4','3/4'] for key in j.PHYSICAL},'features':{key:['2/3','5/6'] for key in m.FEATURES},'budget':limits,'provenance':{'kind':'unit_identity_function_mock','statistical_coverage_claimed':False}}
def setup(folder,**budget):
    path=Path(folder)/'request.json';raw=e.canonical(request_dict(**budget));path.write_bytes(raw);identity=e.sha(raw);return path,identity,e.read_request(path,identity)
class Tests(unittest.TestCase):
    def test_zero_budget_full_root(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td);folder=Path(td)/'states';e.run(q,folder);out=v.recover(p,h,folder,e.source_pins(),normal=True);self.assertEqual(out['physical_union_sup_diameter'],'1/2');self.assertFalse(out['parameter_accuracy_released'])
    def test_invalid_original_has_no_cover(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td);p.write_bytes(p.read_bytes()+b' ');out=v.recover(p,h,Path(td)/'absent',e.source_pins());self.assertEqual(out['status'],'EVIDENCE_INVALID');self.assertIsNone(out['physical_cover']);self.assertIsNone(out['recommended_history'])
    def test_mock_interval_rhs_and_replay(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ad,'evaluate',side_effect=identity_ad):
            p,h,q=setup(td,max_operations=1);folder=Path(td)/'states';e.run(q,folder);out=v.recover(p,h,folder,e.source_pins(),normal=True)
            self.assertEqual(out['details']['operations_recomputed'],1)
            for key,bounds in out['physical_cover'][0]['box'].items():self.assertLessEqual(e.F(bounds[0]),e.F(1,3));self.assertGreaterEqual(e.F(bounds[1]),e.F(2,3))
    def test_rehashed_false_preconditioner_witness_rejected(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ad,'evaluate',side_effect=identity_ad):
            p,h,q=setup(td,max_operations=1);folder=Path(td)/'states';e.run(q,folder);old=sorted(folder.glob('state-*.json'))[-1];payload=e.read_json(old);payload['events'][-1]['detail']['fixed_rational_Y'][0][0]='0';raw=e.canonical(payload);fake=folder/f"state-{payload['sequence']:05d}-{e.sha(raw)}.json";fake.write_bytes(raw)
            with self.assertRaises(v.InvalidCertificate):v.valid_checkpoint(fake,q,e.source_pins(),time.monotonic()+1,16)
    def test_precommit_failure_keeps_full_inflight_parent(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ad,'evaluate',side_effect=identity_ad):
            p,h,q=setup(td,max_operations=1);folder=Path(td)/'states'
            def fail(stage,payload):
                if stage=='before_commit' and payload['events'] and payload['events'][-1]['kind']=='applied':raise OSError('tiny precommit fault')
            with self.assertRaises(OSError):e.run(q,folder,hook=fail)
            out=v.recover(p,h,folder,e.source_pins());self.assertTrue(out['details']['inflight_pre_state_retained']);self.assertEqual(out['physical_union_sup_diameter'],'1/2')
    def test_refusal_preserves_prestate(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ad,'evaluate',side_effect=m.Unsupported('tiny forced arithmetic refusal')):
            p,h,q=setup(td,max_operations=1);folder=Path(td)/'states';e.run(q,folder);out=v.recover(p,h,folder,e.source_pins(),normal=True);self.assertEqual(out['physical_union_sup_diameter'],'1/2');self.assertEqual(out['augmented_states'][0]['status'],'unsupported')
    def test_joint_split_keeps_untouched_other_child(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ad,'evaluate',side_effect=identity_ad):
            p,h,q=setup(td,max_operations=2,max_splits=1,preconditioner='zero');folder=Path(td)/'states';e.run(q,folder);out=v.recover(p,h,folder,e.source_pins(),normal=True)
            self.assertEqual(len(out['physical_cover']),2);self.assertEqual(out['physical_union_sup_diameter'],'1/2');self.assertEqual(out['details']['splits'],1)
    def test_replay_budget_discards_all_narrowing(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ad,'evaluate',side_effect=identity_ad):
            p,h,q=setup(td,max_operations=1,recovery_max_operations=0);folder=Path(td)/'states';e.run(q,folder);out=v.recover(p,h,folder,e.source_pins());self.assertEqual(out['mode'],'recovered_authenticated_root');self.assertEqual(out['physical_union_sup_diameter'],'1/2')
if __name__=='__main__':unittest.main()
