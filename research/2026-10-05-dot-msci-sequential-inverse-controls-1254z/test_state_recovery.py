import json,tempfile,time,unittest
from pathlib import Path
from unittest.mock import patch
import seq_engine as e
import seq_check as v
import contractors as ops
import interval_math as m

def request_dict(**budget):
    limits=dict(max_operations=0,max_splits=0,max_depth=2,sweeps_per_cell=1,wall_ms=1000,recovery_wall_ms=1000,recovery_max_operations=64);limits.update(budget)
    box={key:['1','2'] for key in ops.PHYSICAL};box['g']=['1/4','3/4']
    return {'schema':e.SCHEMA,'model':e.MODEL,'quantity':'shifted_bernoulli_character_mean','box':box,'features':{key:['0','1'] for key in m.FEATURES},'budget':limits,'provenance':{'kind':'unit_geometry_mock','statistical_coverage':False}}
def setup(folder,**budget):
    p=Path(folder)/'request.json';raw=e.canonical(request_dict(**budget));p.write_bytes(raw);h=e.sha(raw);return p,h,e.read_request(p,h)
def same(state,kind):return ops.clone(state),{}
class Tests(unittest.TestCase):
    def test_schema_and_original_identity(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td)
            self.assertEqual(len(q['physical']),9);self.assertEqual(len(q['observations']),9)
            with self.assertRaises(ValueError):e.read_request(p,'0'*64)
            data=request_dict();del data['features']['AC2'];p.write_bytes(e.canonical(data))
            with self.assertRaises(ValueError):e.read_request(p,e.sha(p.read_bytes()))
    def test_zero_budget_preserves_full_root(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td);states=Path(td)/'states';e.run(q,states);out=v.recover(p,h,states,e.source_pins(),normal=True)
            self.assertEqual(out['status'],'UNKNOWN_OUTER_COVER');self.assertEqual(out['physical_union_sup_diameter'],'1');self.assertFalse(out['parameter_accuracy_released'])
    def test_initial_range_inconsistency_is_replayed(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'request.json';d=request_dict();d['features']['AC1']=['0','1/4'];p.write_bytes(e.canonical(d));h=e.sha(p.read_bytes());q=e.read_request(p,h);states=Path(td)/'states';e.run(q,states);out=v.recover(p,h,states,e.source_pins(),normal=True)
            self.assertEqual(out['status'],'EMPTY_COMPATIBLE_SET')
    def test_precommit_failure_retains_inflight_prestate(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td,max_operations=1);states=Path(td)/'states'
            def fail(stage,payload):
                if stage=='before_commit' and payload['events'] and payload['events'][-1]['kind']=='applied':raise OSError('tiny precommit failure')
            with self.assertRaises(OSError):e.run(q,states,hook=fail)
            out=v.recover(p,h,states,e.source_pins());self.assertEqual(out['status'],'RECOVERED_UNKNOWN');self.assertTrue(out['details']['inflight_pre_state_retained']);self.assertEqual(out['physical_union_sup_diameter'],'1')
    def test_postcommit_failure_preserves_contracted_state(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td,max_operations=1);states=Path(td)/'states'
            def fail(stage,payload):
                if stage=='after_commit' and payload['events'] and payload['events'][-1]['kind']=='applied':raise OSError('tiny postcommit failure')
            with self.assertRaises(OSError):e.run(q,states,hook=fail)
            out=v.recover(p,h,states,e.source_pins());self.assertEqual(out['details']['operations_recomputed'],1)
    def test_forged_rehashed_contraction_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td,max_operations=1);states=Path(td)/'states';e.run(q,states);last=sorted(states.glob('state-*.json'))[-1];data=e.read_json(last);data['events'][-1]['post_state']['physical']['rA']=['1','1'];data['frontier'][0]['state']['physical']['rA']=['1','1'];raw=e.canonical(data);fake=states/f"state-{data['sequence']:05d}-{e.sha(raw)}.json";fake.write_bytes(raw)
            with self.assertRaises(v.InvalidCertificate):v.valid_checkpoint(fake,q,e.source_pins(),time.monotonic()+1,64)
    def test_refusal_does_not_commit_partial_clone(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td,max_operations=1);states=Path(td)/'states'
            def refuse(state,kind):
                partial=ops.clone(state);partial['physical']['rA']=m.I.point(1);raise m.Unsupported('mock resource refusal')
            e.run(q,states,operator=refuse);data=e.read_json(sorted(states.glob('state-*.json'))[-1]);self.assertEqual(data['frontier'][0]['state']['physical']['rA'],['1','2']);self.assertEqual(data['frontier'][0]['status'],'unsupported')
    def test_changed_input_has_no_cover(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td);p.write_bytes(p.read_bytes()+b' ');out=v.recover(p,h,Path(td)/'missing',e.source_pins());self.assertEqual(out['status'],'EVIDENCE_INVALID');self.assertIsNone(out['physical_cover'])
    def test_recovery_budget_falls_back_to_original_physical_union(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td,max_operations=1,recovery_max_operations=0);states=Path(td)/'states';e.run(q,states);out=v.recover(p,h,states,e.source_pins());self.assertEqual(out['mode'],'recovered_authenticated_root');self.assertTrue(out['details']['all_inherited_contractions_discarded'])
    def test_mock_split_includes_both_children(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td,max_operations=13,max_splits=1);states=Path(td)/'states'
            with patch.object(ops,'operate',side_effect=same):
                e.run(q,states,operator=same);out=v.recover(p,h,states,e.source_pins(),normal=True)
            self.assertEqual(len(out['physical_cover']),2);self.assertEqual(out['physical_union_sup_diameter'],'1');self.assertEqual(out['details']['splits'],1)
if __name__=='__main__':unittest.main()
