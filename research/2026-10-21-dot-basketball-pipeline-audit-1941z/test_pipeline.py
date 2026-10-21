"""Implementation fixtures only. These are not new sports model evidence."""
import copy,json,tempfile,unittest
from pathlib import Path
import numpy as np
from portability_pipeline import audit,History,contexts,run,fit
from value_framework import deployment_value,exposure_value,scenario_envelope

def fixture():
 rows=[];games=[];history=[]
 for i in range(1,13):
  day=f'2020-01-{i:02d}';gid=f'g{i}'
  a=[f'A{j}' for j in range(5)];b=[f'B{j}' for j in range(5)]
  ap=9+i%3;bp=8+i%4
  games.append(dict(game_id=gid,date=day,season='2019-20',home_team='A',away_team='B',home_points=ap,away_points=bp))
  for side,off,de,pts in [('A',a,b,ap),('B',b,a,bp)]:
   rows.append(dict(game_id=gid,stint_id=side,date=day,season='2019-20',off_team=side,def_team='B' if side=='A' else 'A',offense=off,defense=de,points=pts,possessions=10,home=int(side=='A'),period=1,score_margin=0))
  for j,p in enumerate(a+b):history.append(dict(game_id=gid,date=day,player_id=p,three_pa=(j+i)%4,fga=8))
 return {'provenance':{'kind':'implementation_fixture','source':'original artificial unit-test records','permission_basis':'original generated test fixture'},'rows':rows,'games':games,'history':history}

class Checks(unittest.TestCase):
 def setUp(self):self.f=fixture()
 def audit(self):return audit(self.f['rows'],self.f['games'],self.f['history'])
 def test_complete_scores(self):self.assertTrue(self.audit()['score_reconciled'])
 def test_duplicate_row_rejected(self):
  self.f['rows'].append(self.f['rows'][0]);self.assertRaises(ValueError,self.audit)
 def test_ten_unique_players(self):
  self.f['rows'][0]['offense'][0]='B0';self.assertRaises(ValueError,self.audit)
 def test_zero_possession_rejected(self):
  self.f['rows'][0]['possessions']=0;self.assertRaises(ValueError,self.audit)
 def test_score_reconciliation(self):
  self.f['rows'][0]['points']+=1;self.assertRaises(ValueError,self.audit)
 def test_explicit_season_required(self):
  del self.f['games'][0]['season'];self.assertRaises(ValueError,self.audit)
 def test_bubble_season_respects_source_label(self):
  for r in self.f['rows']:r['date']=r['date'].replace('2020-01','2020-08')
  for g in self.f['games']:g['date']=g['date'].replace('2020-01','2020-08')
  from portability_pipeline import Design
  d=Design(self.f['rows'],contexts(self.f['rows'],History(self.f['history'])),'common_context')
  self.assertEqual(d.seasons,['2019-20'])
 def test_scenario_envelope_common_effect(self):
  p=dict(a=0.,b=0.,u=0.,rate=.5);r=dict(a=0.,b=0.,u=0.,rate=.3);t=[dict(u=0.,rate=.4)]*4
  v=scenario_envelope([p],[r],[t],[.35],[dict(minutes_per_game=24,games_available=10,pace_per48=100)],[.2])
  self.assertAlmostEqual(v['net_points_per100_range'][0],.8)
 def test_date_mismatch(self):
  self.f['rows'][0]['date']='2020-01-02';self.assertRaises(ValueError,self.audit)
 def test_invalid_shot_history(self):
  self.f['history'][0]['three_pa']=9;self.assertRaises(ValueError,self.audit)
 def test_same_day_history_excluded(self):
  h=History(self.f['history']);self.assertEqual(h.rate('A0','2020-01-01'),.35)
 def test_frozen_history_excludes_later_games(self):
  h=History(self.f['history']);r=self.f['rows'][-1]
  c=contexts([r],h,'2020-01-05')[0]
  self.assertTrue(np.allclose(c,h.contexts(r,'2020-01-05')))
 def test_full_pipeline_and_future_feature_invariance(self):
  f=self.f;r,p=run(f['rows'],f['games'],f['history'],'2020-01-04','2020-01-08')
  h=f['history']+[dict(game_id='future',date='2020-02-01',player_id='A0',three_pa=100000,fga=100000)]
  r2,p2=run(f['rows'],f['games'],h,'2020-01-04','2020-01-08')
  self.assertEqual(p,p2);self.assertEqual(r,r2)
  self.assertEqual(len(p),24);self.assertEqual(len(r['models']),3)
 def test_test_labels_do_not_change_selection_or_coefficients(self):
  f=self.f;r,_=run(f['rows'],f['games'],f['history'],'2020-01-04','2020-01-08')
  for row in f['rows']:
   if row['date']>'2020-01-08':row['points']+=1
  for game in f['games']:
   if game['date']>'2020-01-08':game['home_points']+=1;game['away_points']+=1
  r2,_=run(f['rows'],f['games'],f['history'],'2020-01-04','2020-01-08')
  for m in r['models']:
   self.assertEqual(r['models'][m]['selected_lambda'],r2['models'][m]['selected_lambda'])
   self.assertEqual(r['models'][m]['player_coefficients'],r2['models'][m]['player_coefficients'])
 def test_empty_partition(self):
  f=self.f;self.assertRaises(ValueError,run,f['rows'],f['games'],f['history'],'2019-01-01','2019-02-01')
 def test_defensive_sign_and_spillovers(self):
  p=dict(a=.02,b=-.01,u=.03,rate=.5);r=dict(a=0.,b=0.,u=0.,rate=.3)
  t=[dict(u=.04,rate=.4)]*4
  v=deployment_value(p,r,t,.35)
  self.assertAlmostEqual(v['defense_points_saved_per100'],1)
  self.assertAlmostEqual(v['teammate_spillover_per100'],.8)
  self.assertAlmostEqual(v['net_points_per100'],3.95)
  # Direct five-player interaction recomputation agrees with closed form.
  def score(five):return sum(q.get('a',0)+q['u']*(sum(x['rate'] for x in five if x is not q)/4-.35) for q in five)
  # use distinct dictionary objects for identity-based exclusion
  t=[dict(u=.04,rate=.4,a=0.) for _ in range(4)]
  self.assertAlmostEqual(100*(score([p]+t)-score([r]+t)),v['offense_points_per100'])
 def test_common_context_recomputed(self):
  p=dict(a=0.,b=0.,u=0.,rate=.5);r=dict(a=0.,b=0.,u=0.,rate=.3);t=[dict(u=0.,rate=.4)]*4
  v=deployment_value(p,r,t,.35,common_context_coef=.2)
  self.assertAlmostEqual(v['net_points_per100'],.8)
 def test_zero_exposure_and_no_automatic_wins(self):
  v=exposure_value(3,24,0,100);self.assertEqual(v['net_points_above_stated_reference'],0);self.assertIsNone(v['wins_above_stated_reference'])
 def test_exposure_scale(self):
  v=exposure_value(3,24,10,100);self.assertEqual(v['on_court_possessions'],500);self.assertEqual(v['net_points_above_stated_reference'],15)
 def test_negative_exposure_rejected(self):self.assertRaises(ValueError,exposure_value,3,-1,10,100)

if __name__=='__main__':unittest.main(verbosity=2)
