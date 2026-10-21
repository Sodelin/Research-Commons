import copy,unittest
from compose import compose,COMPONENTS
class Test(unittest.TestCase):
 def setUp(self):
  self.r=dict(player_id='synthetic-two-way',window_start='2025-05-01',window_end='2025-06-30',window_convention='[start,end)',mode='forecast',reference_id='fixture',accounting_version='fixture-v1',runs_per_win=10,conversion_source='synthetic convention',components={})
  for name in COMPONENTS:self.r['components'][name]=dict(status='available',value=1.,units='runs',mode='forecast',reference_id='fixture',accounting_version='fixture-v1',source='synthetic fixture, not MLB',definition=name)
  for v in self.r['components'].values():
   for k in ['player_id','window_start','window_end','window_convention']:v[k]=self.r[k]
 def test_complete(self):
  x=compose(self.r);self.assertEqual(x['total_runs'],7);self.assertEqual(x['wins'],.7)
 def test_missing_not_zero(self):
  del self.r['components']['fielding'];x=compose(self.r);self.assertIsNone(x['total_runs']);self.assertIsNone(x['wins']);self.assertEqual(x['supported_subtotal_runs'],6)
 def test_boolean(self):
  self.r['components']['batting']['value']=True
  with self.assertRaises(ValueError):compose(self.r)
 def test_window(self):
  self.r['components']['batting']['window_end']='2025-07-01'
  with self.assertRaises(ValueError):compose(self.r)
 def test_partial(self):
  self.r['components']['baserunning']['status']='partial';x=compose(self.r);self.assertEqual(x['supported_subtotal_runs'],7);self.assertIsNone(x['total_runs'])
 def test_overlap(self):
  self.r['components']['WAR']=self.r['components']['batting']
  with self.assertRaises(ValueError):compose(self.r)
 def test_reference(self):
  self.r['components']['pitching']['reference_id']='different'
  with self.assertRaises(ValueError):compose(self.r)
 def test_mode(self):
  self.r['components']['pitching']['mode']='retrospective'
  with self.assertRaises(ValueError):compose(self.r)
 def test_version(self):
  self.r['components']['fielding']['accounting_version']='old framing'
  with self.assertRaises(ValueError):compose(self.r)
 def test_nan(self):
  self.r['components']['batting']['value']=float('nan')
  with self.assertRaises(ValueError):compose(self.r)
 def test_not_applicable(self):
  self.r['components']['pitching'].update(status='not_applicable',reason='synthetic player explicitly assumed not to pitch');self.assertEqual(compose(self.r)['total_runs'],6)
 def test_unsupported_absence(self):
  self.r['components']['pitching']=dict(status='not_applicable')
  with self.assertRaises(ValueError):compose(self.r)
if __name__=='__main__':unittest.main()
