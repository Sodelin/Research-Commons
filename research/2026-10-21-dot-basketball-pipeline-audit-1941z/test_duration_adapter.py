import unittest
from duration_net_adapter import integrate_game
class Checks(unittest.TestCase):
 def rows(self):
  a=[f'A{i}' for i in range(5)];b=[f'B{i}' for i in range(5)];c=b[:4]+['B5']
  base=[dict(game_id='g',quarter=1,side='home',order=0,seconds=720,lineup=a,pm=3),dict(game_id='g',quarter=1,side='away',order=0,seconds=240,lineup=b,pm=-1),dict(game_id='g',quarter=1,side='away',order=1,seconds=480,lineup=c,pm=-2)]
  return [{**r,'quarter':q} for q in range(1,5) for r in base]
 def test_original_target_not_split(self):
  rs=integrate_game(self.rows(),12);self.assertEqual(len(rs),4);self.assertEqual(rs[0]['observed_home_pm'],3)
  self.assertEqual(rs[0]['opponent_player_seconds']['B4'],240);self.assertEqual(rs[0]['opponent_player_seconds']['B5'],480)
  self.assertEqual(rs[0]['home_net_points_per48'],12)
 def test_truncated_quarter(self):
  rs=self.rows();rs[0]['seconds']=719;self.assertRaises(ValueError,integrate_game,rs)
 def test_margin_mismatch(self):self.assertRaises(ValueError,integrate_game,self.rows(),5)
 def test_order_duplicate(self):
  rs=self.rows();rs[2]['order']=0;self.assertRaises(ValueError,integrate_game,rs)
 def test_noncomplementary_pm(self):
  rs=self.rows();rs[0]['pm']=4;self.assertRaises(ValueError,integrate_game,rs)
if __name__=='__main__':unittest.main(verbosity=2)
