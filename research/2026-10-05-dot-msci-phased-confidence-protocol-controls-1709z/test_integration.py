import copy,tempfile,unittest
from pathlib import Path
from fractions import Fraction as F
import integration_core as c
import prepare_input as p

def panel():return {'schema':'complete-six-copy-two-site-loci-v1','loci':[{'id':'locus1','columns':[1,2],'calls':{k:'AA' for k in c.LABELS}},{'id':'locus2','columns':[3,7],'calls':dict(A1='AG',A2='CA',B1='GA',B2='TT',C1='CT',C2='GG')}]}
def selection(data):return c.sha(c.canonical([{'id':x['id'],'columns':x['columns']} for x in data['loci']]))
def counts(m=100):return {'complete_extraction':True,'feature_order':list(c.FEATURES),'m':m,'counts':{k:m for k in c.FEATURES}}
class Tests(unittest.TestCase):
    def test_literal_correlated_parities(self):
        d=panel();r=c.extract(d,2,selection(d));self.assertEqual(r['counts'],dict(AC1=2,AC2=2,CC1=1,BC1=1,BC2=2,AB1=1,AB2=2,AA1=2,BB1=2));self.assertFalse(r['within_locus_feature_independence_assumed'])
    def test_duplicate_id_and_wrong_calls_rejected(self):
        for change in [lambda d:d['loci'][1].update(id='locus1'),lambda d:d['loci'][1]['calls'].update(A1='AN'),lambda d:d['loci'][1]['calls'].pop('C2'),lambda d:d['loci'][1]['calls'].update(A1='aa'),lambda d:d['loci'][1].update(columns=[2,2])]:
            d=panel();change(d)
            with self.assertRaises(c.EvidenceInvalid):c.extract(d,2,selection(d))
    def test_incomplete_stream_no_counts(self):
        d=panel();d['loci'].pop()
        with self.assertRaises(c.EvidenceInvalid):c.extract(d,2,selection(d))
    def test_same_strings_different_ids_allowed(self):
        d=panel();d['loci'][1]['calls']=dict(d['loci'][0]['calls']);r=c.extract(d,2,selection(d));self.assertEqual(set(r['counts'].values()),{2})
    def test_selection_binding(self):
        with self.assertRaises(c.EvidenceInvalid):c.extract(panel(),2,'0'*64)
    def test_duplicate_json_key_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            q=Path(td)/'x';raw=b'{"x":1,"x":2}';q.write_bytes(raw)
            with self.assertRaises(c.EvidenceInvalid):c.read(q,c.sha(raw))
    def test_nonfinite_and_float_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            q=Path(td)/'x'
            for raw in [b'{"x":NaN}',b'{"x":0.1}']:
                q.write_bytes(raw)
                with self.assertRaises(c.EvidenceInvalid):c.read(q,c.sha(raw))
    def test_union_bound_and_variable_delta(self):
        a=c.confidence(counts(),F(1,10),16);b=c.confidence(counts(),F(1,1000),16)
        self.assertEqual(a['union_factor'],18);self.assertLessEqual(F(a['error_upper_bound']),F(1,10));self.assertLessEqual(F(b['error_upper_bound']),F(1,1000));self.assertGreaterEqual(F(b['radius']),F(a['radius']));self.assertFalse(a['within_locus_feature_independence_assumed'])
        for z in (a,b):
            good=[r for r in z['search'] if r['certified']];self.assertTrue(good);self.assertTrue(all(18*F(r['exp_interval'][1])<=F(z['delta']) for r in good))
    def test_full_range_fallback_without_false_inequality(self):
        z=c.confidence(counts(1),F(1,10),12);self.assertEqual(z['mode'],'FULL_RANGE_CERTIFIED');self.assertEqual(set(tuple(x) for x in z['shifted_mean_box'].values()),{('0','1')});self.assertEqual(z['error_upper_bound'],'0')
    def test_zero_search_and_arithmetic_refusal(self):
        z=c.confidence(counts(),F(1,10),0);self.assertEqual(z['mode'],'FULL_RANGE_CERTIFIED')
        def refuse(*_):raise ValueError('tiny arithmetic refusal')
        z=c.confidence(counts(),F(1,10),12,exp_neg=refuse);self.assertEqual(z['mode'],'FULL_RANGE_CERTIFIED');self.assertEqual(z['arithmetic_refusal'],'ValueError')
    def test_radius_independent_of_counts(self):
        a=counts();b=counts();b['counts']={k:0 for k in c.FEATURES};x=c.confidence(a,F(1,10),12);y=c.confidence(b,F(1,10),12);self.assertEqual(x['radius'],y['radius']);self.assertEqual(x['search'],y['search']);self.assertTrue(all(v['empty'] for v in y['raw_moment_projection'].values()))
    def test_partial_extraction_receipt_refused(self):
        a=counts();a['complete_extraction']=False
        with self.assertRaises(c.EvidenceInvalid):c.confidence(a,F(1,10),12)
if __name__=='__main__':unittest.main()

class ExactParameterTests(unittest.TestCase):
    def test_float_delta_and_boolean_m_refused(self):
        with self.assertRaises(c.EvidenceInvalid):c.confidence(counts(),0.1,12)
        with self.assertRaises(c.InputResource):c.extract(panel(),True,selection(panel()))
