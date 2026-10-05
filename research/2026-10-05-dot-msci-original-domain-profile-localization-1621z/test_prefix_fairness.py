"""Tiny mocked transitions test conservative same-process replay and fair scheduling."""
import tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import global_engine as e
import global_check as v
import global_contractors as ops
import interval_math as m
from test_journal import setup,noop,fake_latest

def narrow(state,kind,steps):
    state=ops.clone(state);state['physical']['h']=m.I(e.F(1,3),e.F(2,3));return state,{'mock':'certified_test_interval'}
class Tests(unittest.TestCase):
    def test_initialization_before_any_frame_has_no_invented_hash(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td,recovery_wall_ms=0);out=v.recover(p,h,Path(td)/'absent',e.source_pins(),clock=lambda:1)
            # A missing chain is actual evidence failure, even if there is no time to replay it.
            self.assertEqual(out['mode'],'recovered_authenticated_original_domain')
            folder=Path(td)/'journal';e.run(q,folder)
            ticks=iter([0,1]);out=v.recover(p,h,folder,e.source_pins(),clock=lambda:next(ticks))
            self.assertEqual(out['mode'],'recovered_same_process_validated_prefix');self.assertEqual(out['details']['validated_frames'],0);self.assertIsNone(out['details']['last_validated_commit']);self.assertEqual(out['details']['prefix_origin'],'authenticated_original_request_initialization')
    def test_contraction_retained_but_no_accuracy_release(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=narrow):
            p,h,q=setup(td,max_stages=2,recovery_max_stages=1);folder=Path(td)/'journal';e.run(q,folder,operator=narrow);out=v.recover(p,h,folder,e.source_pins(),normal=True)
            self.assertEqual(out['status'],'RECOVERED_UNKNOWN');self.assertEqual(out['details']['stages_recomputed'],1);self.assertEqual(out['details']['validated_frames'],4);self.assertFalse(out['whole_union_width_target_met']);self.assertEqual(out['physical_cover'][0]['box']['h'],['1/3','2/3']);self.assertIsNone(out['ranked_histories'])
    def test_incomplete_mutating_operation_cannot_promote(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td,max_stages=1);folder=Path(td)/'journal';e.run(q,folder,operator=narrow);now=[0]
            def slow(state,kind,steps):
                post,detail=narrow(state,kind,steps);now[0]=2;return post,detail
            with patch.object(ops,'operate',side_effect=slow):out=v.recover(p,h,folder,e.source_pins(),clock=lambda:now[0])
            self.assertEqual(out['details']['validated_frames'],2);self.assertEqual(out['details']['stages_recomputed'],0);self.assertEqual(out['physical_cover'][0]['box']['h'],['1/4','3/4']);self.assertTrue(out['details']['inflight_pre_state_retained'])
    def test_complete_split_keeps_both_children_on_cap(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=noop):
            p,h,q=setup(td,max_stages=12,max_splits=1,recovery_max_stages=11);folder=Path(td)/'journal';e.run(q,folder,operator=noop);out=v.recover(p,h,folder,e.source_pins())
            self.assertEqual(out['details']['splits'],1);self.assertEqual({c['id'] for c in out['physical_cover']},{'r0','r1'});self.assertEqual(out['widths']['h']['width'],'1/2');self.assertEqual([c['birth_order'] for c in out['augmented_states']],[1,2])
    def test_unexamined_numeric_forgery_not_adopted(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=noop):
            p,h,q=setup(td,max_stages=1,recovery_max_stages=0);folder=Path(td)/'journal';e.run(q,folder,operator=noop);fake_latest(folder,lambda d:d['transition']['detail'].update(mock='forged'))
            out=v.recover(p,h,folder,e.source_pins());self.assertEqual(out['mode'],'recovered_same_process_validated_prefix');self.assertEqual(out['details']['ignored_suffix_frames'],1);self.assertEqual(out['widths']['h']['width'],'1/2')
    def test_examined_forgery_discards_all_narrowing(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=narrow):
            p,h,q=setup(td,max_stages=2);folder=Path(td)/'journal';e.run(q,folder,operator=narrow);fake_latest(folder,lambda d:d['transition']['detail'].update(mock='forged'))
            out=v.recover(p,h,folder,e.source_pins());self.assertEqual(out['mode'],'recovered_authenticated_original_domain');self.assertEqual(out['widths']['h']['width'],'1/2')
    def test_identity_mismatch_cannot_keep_prefix(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td);folder=Path(td)/'journal';e.run(q,folder);pins=e.source_pins();pins['global_engine.py']='0'*64;out=v.recover(p,h,folder,pins);self.assertEqual(out['mode'],'recovered_authenticated_original_domain')
    def test_shallow_sibling_precedes_deeper_descendant(self):
        with tempfile.TemporaryDirectory() as td:
            _,_,q=setup(td);root=e.initial_cell(q);frontier={key:{**root,'id':key,'birth_order':birth} for key,birth in [('r00',3),('r01',4),('r1',2)]};self.assertEqual(e.pending_order(frontier),['r1','r00','r01']);self.assertEqual(len(frontier),3)
            frontier['r1']['status']='unsupported';self.assertEqual(e.pending_order(frontier),['r00','r01']);self.assertIn('r1',frontier)
    def test_birth_order_survives_stage_and_children_commit_together(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=noop):
            p,h,q=setup(td,max_stages=24,max_splits=2);folder=Path(td)/'journal';e.run(q,folder,operator=noop);out=v.recover(p,h,folder,e.source_pins(),normal=True);self.assertTrue(out['details']['complete_numeric_replay'])
            frames=[e.read_json(x) for x in sorted(folder.glob('state-*.json'))];splits=[x for x in frames if x['transition']['kind']=='split'];self.assertEqual(len(splits),2)
            second=splits[1];self.assertEqual({c['id'] for c in second['frontier']},{'r00','r01','r1'});following=next(x for x in frames if x['sequence']>second['sequence'] and x['transition']['kind']=='started');self.assertEqual(following['transition']['cell'],'r1')
if __name__=='__main__':unittest.main()
