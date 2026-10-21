import csv,json,tempfile,unittest
from pathlib import Path
from licensed_reference_value import calculate
from duration_net_fit import run
class Checks(unittest.TestCase):
 def test_real_label_gate_rejects_unvalidated_source(self):
  with self.assertRaisesRegex(ValueError,'source-label validation'):run({'provenance':{'kind':'real'}},'2015-12-31','2016-01-31')
 def test_real_possession_label_gate(self):
  from portability_pipeline import run as possession_run
  with self.assertRaisesRegex(ValueError,'source-label validation'):possession_run([],[],[],'2015-12-31','2016-01-31',data_kind='real')
 def test_reference_arithmetic_and_blank_id_preservation(self):
  with tempfile.TemporaryDirectory() as t:
   p=Path(t);board=p/'board.csv'
   board.write_text('rank_all,pid,name,loki,lo90,hi90\n1,123,Known,3,1,5\n2,,Unresolved,2,0,4\n')
   c=dict(reference_label='hypothetical',reference_net_per100=1,scenario_label='fixture',minutes_per_game=24,games_available=10,pace_per48=100)
   rs,m=calculate(board,c,p/'out');self.assertEqual(len(rs),2);self.assertEqual(rs[0]['point_value_vs_reference'],10)
   self.assertEqual(rs[0]['transformed_publisher_low'],0);self.assertEqual(rs[0]['transformed_publisher_high'],20)
   self.assertEqual(m['unresolved_blank_id_rows'],1);self.assertNotEqual(rs[0]['source_row_key'],rs[1]['source_row_key'])
 def test_missing_reference_label_rejected(self):
  with self.assertRaises(ValueError):calculate(Path('unused'),{},Path('unused'))
if __name__=='__main__':unittest.main(verbosity=2)
