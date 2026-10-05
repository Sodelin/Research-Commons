import copy,json,tempfile,time,unittest
from fractions import Fraction as F
from pathlib import Path
from unittest.mock import patch
import filter_core as c
import check_cover as v
import fixture_requests as fixtures

class MockWideProvider:
    class DomainError(ValueError):pass
    class ResourceBound(ValueError):pass
    def evaluate(self,p,bits):
        class I:lo=F(0);hi=F(1)
        return p,None,{pair:[I() for _ in range(55)] for pair in c.PAIRS}
class MockRefusal(MockWideProvider):
    def evaluate(self,p,bits):raise self.ResourceBound('small mock refusal')

class FilterTests(unittest.TestCase):
    def setup_request(self,folder,**kwargs):
        p=Path(folder)/'request.json';d=fixtures.request_dict(**kwargs);h=fixtures.write_request(p,d);return p,h,c.read_request(p,h)
    def core_hash(self):return c.sha(Path(c.__file__).read_bytes())
    def test_full_schema_and_invalid_requests(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,req=self.setup_request(td);self.assertEqual(len(req.box),9);self.assertEqual(len(req.observations),330)
            with self.assertRaises(c.Invalid):c.read_request(p,'0'*64)
            for change in ['dimension','quantity','index','float']:
                d=fixtures.request_dict()
                if change=='dimension':del d['box']['rC']
                elif change=='quantity':d['quantity']='laplace_moment'
                elif change=='index':d['features']['AA'][1]['k']=1
                else:d['box']['h'][0]=0.01
                raw=c.canonical(d);p.write_bytes(raw)
                with self.assertRaises(c.Invalid):c.read_request(p,c.sha(raw))
    def test_exact_time_conversion_and_radius(self):
        with tempfile.TemporaryDirectory() as td:
            _,_,req=self.setup_request(td);centre=c.midpoint(req.box);p=c.absolute_parameters(centre)
            self.assertEqual((p['h'],p['t1'],p['t0']),(F(1,16),F(1,8),F(3,16)));self.assertGreater(c.radius(req.box),0)
    def test_closed_touch_is_not_excluded(self):
        self.assertFalse(c.disjoint((F(0),F(1,2)),(F(1,2),F(1))));self.assertTrue(c.disjoint((F(0),F(1,3)),(F(1,2),F(1))))
    def test_zero_budget_keeps_original_full_box(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,req=self.setup_request(td,max_evaluations=0);folder=Path(td)/'states';c.run_filter(req,folder,MockWideProvider());r=v.certify_or_recover(p,h,folder,self.core_hash(),normal=True)
            self.assertEqual(r['status'],'UNKNOWN_OUTER_COVER');self.assertEqual(r['retained_cover'][0]['box'],c.box_record(req.box));self.assertIsNone(r['ranked_histories'])
    def test_mock_split_cover_and_cell_mesh_not_union(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,req=self.setup_request(td,max_evaluations=3,max_splits=3);folder=Path(td)/'states';c.run_filter(req,folder,MockWideProvider());r=v.certify_or_recover(p,h,folder,self.core_hash(),normal=True)
            self.assertEqual(len(r['retained_cover']),4);self.assertFalse(r['parameter_accuracy_released']);self.assertEqual(r['union_sup_diameter'],'1/64')
            centre=c.midpoint(req.box)
            self.assertTrue(any(all(F(cell['box'][k][0])<=x<=F(cell['box'][k][1]) for k,x in zip(c.COORDS,centre)) for cell in r['retained_cover']))
    def test_refusal_keeps_cell(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,req=self.setup_request(td);folder=Path(td)/'states';c.run_filter(req,folder,MockRefusal());r=v.certify_or_recover(p,h,folder,self.core_hash(),normal=True)
            self.assertEqual(len(r['retained_cover']),1);self.assertEqual(r['retained_cover'][0]['status'],'unsupported')
    def test_fault_before_split_commit_recovers_parent(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,req=self.setup_request(td);folder=Path(td)/'states'
            def fail(stage,payload):
                if stage=='before_commit' and payload['events'] and payload['events'][-1]['kind']=='split':raise OSError('tiny injected precommit failure')
            with self.assertRaises(OSError):c.run_filter(req,folder,MockWideProvider(),hook=fail)
            r=v.certify_or_recover(p,h,folder,self.core_hash(),normal=False)
            self.assertEqual(r['status'],'RECOVERED_UNKNOWN');self.assertEqual([x['id'] for x in r['retained_cover']],['r']);self.assertTrue(r['details']['inflight_cell_included'])
    def test_fault_after_split_commit_keeps_both_children(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,req=self.setup_request(td);folder=Path(td)/'states'
            def fail(stage,payload):
                if stage=='after_commit' and payload['events'] and payload['events'][-1]['kind']=='split':raise OSError('tiny postcommit failure')
            with self.assertRaises(OSError):c.run_filter(req,folder,MockWideProvider(),hook=fail)
            r=v.certify_or_recover(p,h,folder,self.core_hash(),normal=False);self.assertEqual([x['id'] for x in r['retained_cover']],['r0','r1'])
    def test_recovery_budget_falls_back_to_authenticated_root(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,req=self.setup_request(td,recovery_wall_ms=0);folder=Path(td)/'states';c.run_filter(req,folder,MockWideProvider());r=v.certify_or_recover(p,h,folder,self.core_hash(),normal=False)
            self.assertEqual(r['mode'],'recovered_authenticated_root');self.assertEqual(r['retained_cover'][0]['box'],c.box_record(req.box))
    def test_changed_original_has_no_cover(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,req=self.setup_request(td);p.write_bytes(p.read_bytes()+b' ');r=v.certify_or_recover(p,h,Path(td)/'missing',self.core_hash())
            self.assertEqual(r['status'],'EVIDENCE_INVALID');self.assertIsNone(r['retained_cover'])
    def test_dropped_child_self_rehashed_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            p,h,req=self.setup_request(td,max_evaluations=1);folder=Path(td)/'states';c.run_filter(req,folder,MockWideProvider());old=sorted(folder.glob('state-*.json'))[-1];payload,_=c.read_json(old);payload['frontier'].pop();raw=c.canonical(payload);new=folder/f"state-{payload['sequence']:05d}-{c.sha(raw)}.json";new.write_bytes(raw)
            with self.assertRaises(v.BadCertificate):v.validate_checkpoint(new,req,self.core_hash(),time.monotonic()+10,32)
    def test_rehashed_false_arithmetic_witness_rejected(self):
        # One published-point forward call, not a filter trial; no inverse search.
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'request.json';d=fixtures.request_dict(kind='point')
            for rows in d['features'].values():
                for row in rows:row['bounds']=['0','0']
            h=fixtures.write_request(p,d);req=c.read_request(p,h);cell=c.Cell('r',req.box);w=c.witness_for(cell,req,c.load_forward());self.assertIsNotNone(w)
            w['point_interval']=['1','1']
            events=[{'kind':'started','cell':'r'},{'kind':'excluded','cell':'r','witness':w}];store=c.Store(Path(td)/'states',req,self.core_hash());file=store.commit(events,{})
            with self.assertRaises(v.BadCertificate):v.validate_checkpoint(file,req,self.core_hash(),time.monotonic()+10,32)
            r=v.certify_or_recover(p,h,file.parent,self.core_hash(),normal=False);self.assertEqual(r['mode'],'recovered_authenticated_root');self.assertEqual(len(r['retained_cover']),1)
if __name__=='__main__':unittest.main()
