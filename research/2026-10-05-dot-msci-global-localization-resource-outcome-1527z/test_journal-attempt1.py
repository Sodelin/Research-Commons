"""Mocked operators test ancestry, cover geometry and target semantics only."""
import tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import global_engine as e
import global_check as v
import global_contractors as ops
import interval_math as m

def request_dict(**budget):
    limits=dict(scalar_steps=2,max_stages=0,max_splits=0,max_states=8,max_depth=4,wall_ms=1000,recovery_wall_ms=1000,recovery_max_stages=32);limits.update(budget)
    return {'schema':e.SCHEMA,'model':e.MODEL,'quantity':'shifted_bernoulli_character_mean','box':{key:['1/4','3/4'] for key in ops.PHYSICAL},'features':{key:['2/3','5/6'] for key in ops.FEATURES},'normalized_width_targets':{key:'1/20' for key in ops.PHYSICAL},'budget':limits,'provenance':{'kind':'unit_geometry_mock','statistical_coverage_claimed':False}}
def setup(folder,**budget):
    p=Path(folder)/'request.json';raw=e.canonical(request_dict(**budget));p.write_bytes(raw);h=e.sha(raw);return p,h,e.read_request(p,h)
def noop(state,kind,steps):return ops.clone(state),{'mock':'no_narrowing'}
def fake_latest(folder,change):
    old=sorted(folder.glob('state-*.json'))[-1];data=e.read_json(old);change(data);raw=e.canonical(data);new=folder/f"state-{data['sequence']:06d}-{e.sha(raw)}.json";new.write_bytes(raw);old.unlink();return new
class Tests(unittest.TestCase):
    def test_zero_budget_original_domain(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td);folder=Path(td)/'journal';e.run(q,folder);out=v.recover(p,h,folder,e.source_pins(),normal=True);self.assertEqual(out['status'],'UNKNOWN_OUTER_COVER');self.assertEqual(out['details']['journal_frames'],1)
    def test_empty_is_never_width_success(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'request.json';d=request_dict();d['features']['AC1']=['0','1/4'];p.write_bytes(e.canonical(d));h=e.sha(p.read_bytes());q=e.read_request(p,h);folder=Path(td)/'journal';e.run(q,folder);out=v.recover(p,h,folder,e.source_pins(),normal=True);self.assertEqual(out['status'],'EMPTY_COMPATIBLE_SET');self.assertFalse(out['whole_union_width_target_met']);self.assertTrue(all(x['width'] is None for x in out['widths'].values()))
    def test_goal_uses_whole_exported_union(self):
        with tempfile.TemporaryDirectory() as td:
            _,_,q=setup(td);cell=e.initial_cell(q);a=e.owned_state_copy(cell['state']);b=e.owned_state_copy(cell['state'])
            for key in ops.PHYSICAL:a['physical'][key]=m.I(e.F(1,4),e.F(13,50));b['physical'][key]=m.I(e.F(37,50),e.F(3,4))
            frontier={'r0':{**cell,'id':'r0','state':a},'r1':{**cell,'id':'r1','state':b}};met,widths=e.goal(q,frontier);self.assertFalse(met);self.assertEqual(widths['h']['width'],'1/2')
    def test_valid_complete_chain_replayed(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=noop):
            p,h,q=setup(td,max_stages=2);folder=Path(td)/'journal';e.run(q,folder,operator=noop);out=v.recover(p,h,folder,e.source_pins(),normal=True);self.assertEqual(out['details']['journal_frames'],5);self.assertEqual(out['details']['stages_recomputed'],2)
    def test_missing_ancestor_discards_all_narrowing(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=noop):
            p,h,q=setup(td,max_stages=1);folder=Path(td)/'journal';e.run(q,folder,operator=noop);sorted(folder.glob('state-*.json'))[1].unlink();out=v.recover(p,h,folder,e.source_pins());self.assertEqual(out['mode'],'recovered_authenticated_original_domain');self.assertTrue(out['details']['all_inherited_narrowing_discarded'])
    def test_rehashed_false_witness_is_not_authenticated_by_hash(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=noop):
            p,h,q=setup(td,max_stages=1);folder=Path(td)/'journal';e.run(q,folder,operator=noop)
            fake_latest(folder,lambda data:data['transition']['detail'].update(mock='forged'))
            out=v.recover(p,h,folder,e.source_pins());self.assertEqual(out['mode'],'recovered_authenticated_original_domain')
    def test_unsafe_parent_name_rejected(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=noop):
            p,h,q=setup(td,max_stages=1);folder=Path(td)/'journal';e.run(q,folder,operator=noop)
            fake_latest(folder,lambda data:data['parent'].update(name='../outside.json'))
            out=v.recover(p,h,folder,e.source_pins());self.assertEqual(out['mode'],'recovered_authenticated_original_domain')
    def test_auxiliary_split_keeps_both_complete_children(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=noop):
            p,h,q=setup(td,max_stages=12,max_splits=1);folder=Path(td)/'journal';e.run(q,folder,operator=noop);out=v.recover(p,h,folder,e.source_pins(),normal=True);self.assertEqual(out['details']['splits'],1);self.assertEqual(len(out['physical_cover']),2);self.assertEqual(out['widths']['h']['width'],'1/2')
    def test_interrupted_precommit_keeps_inflight_parent(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=noop):
            p,h,q=setup(td,max_stages=1);folder=Path(td)/'journal'
            def fail(stage,data):
                if stage=='before_commit' and data['transition']['kind']=='applied':raise OSError('tiny precommit fault')
            with self.assertRaises(OSError):e.run(q,folder,operator=noop,hook=fail)
            out=v.recover(p,h,folder,e.source_pins());self.assertTrue(out['details']['inflight_pre_state_retained']);self.assertEqual(out['widths']['h']['width'],'1/2')
    def test_mutating_refusal_cannot_change_prestate(self):
        def bad(state,kind,steps):state['physical']['h'].lo=e.F(1,2);raise m.Unsupported('tiny deliberate mutation/refusal')
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=bad):
            p,h,q=setup(td,max_stages=1);folder=Path(td)/'journal';e.run(q,folder,operator=bad);out=v.recover(p,h,folder,e.source_pins(),normal=True);self.assertEqual(out['physical_cover'][0]['box']['h'],['1/4','3/4'])
    def test_changed_original_has_no_cover(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,q=setup(td);p.write_bytes(p.read_bytes()+b' ');out=v.recover(p,h,Path(td)/'none',e.source_pins());self.assertEqual(out['status'],'EVIDENCE_INVALID');self.assertIsNone(out['physical_cover'])
    def test_replay_count_refusal_uses_original_domain(self):
        with tempfile.TemporaryDirectory() as td,patch.object(ops,'operate',side_effect=noop):
            p,h,q=setup(td,max_stages=1,recovery_max_stages=0);folder=Path(td)/'journal';e.run(q,folder,operator=noop);out=v.recover(p,h,folder,e.source_pins());self.assertEqual(out['mode'],'recovered_authenticated_original_domain')
if __name__=='__main__':unittest.main()
