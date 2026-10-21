"""Paired held-out diagnostic, no refitting or test-set parameter changes."""
import json,csv
from pathlib import Path
from collections import defaultdict
import numpy as np
from duration_net_adapter import integrate_game
from duration_net_fit import design
p=Path(__file__).resolve().parent
d=json.loads((p/'institutional-adapted.json').read_text());fit=json.loads((p/'real-net-fit.json').read_text())
if 'QUARANTINED' in fit.get('status',''):raise ValueError('Cannot evaluate quarantined source labels as game outcomes')
rows=[];split_counts=defaultdict(int);training_seconds=defaultdict(float);training_games=defaultdict(set)
for g in d['games']:
 split='train' if g['date']<='2015-12-31' else ('validation' if g['date']<='2016-01-31' else 'test');split_counts[split]+=1
 rs=integrate_game(g['segments'],g['home_margin'])
 if split!='test':
  for r in rs:
   for player in r['home_lineup']:training_seconds[player]+=r['seconds'];training_games[player].add(g['game_id'])
   for player,seconds in r['opponent_player_seconds'].items():training_seconds[player]+=seconds;training_games[player].add(g['game_id'])
 else:rows.extend(rs)
games=defaultdict(dict)
for model,m in fit['models'].items():
 players=sorted(m['player_coefficients_per48']);b=np.array([m['home_intercept_per48']]+[m['player_coefficients_per48'][x] for x in players]);X,_=design(rows,players);pred=X@b
 for r,y in zip(rows,pred):
  gid=r['game_id'];games[gid].setdefault('actual',0);games[gid].setdefault(model,0)
  if model=='home_intercept_only':games[gid]['actual']+=r['observed_home_pm']
  games[gid][model]+=float(y*r['seconds']/2880)
errors=np.array([[(v[m]-v['actual'])**2 for m in ['home_intercept_only','duration_adjusted_ridge']] for v in games.values()])
difference=errors[:,1]-errors[:,0]
rng=np.random.default_rng(20261021);boot=np.array([difference[rng.integers(0,len(difference),len(difference))].mean() for _ in range(2000)])
coefs=fit['models']['duration_adjusted_ridge']['player_coefficients_per48']
test_players={x for r in rows for x in r['home_lineup']+list(r['opponent_player_seconds'])}
out={'status':'Actual retrospective NBA derived-data net-rate diagnostic; not new-model superiority',
'cutoffs':{'train_end':'2015-12-31','validation_end':'2016-01-31'},'game_counts':dict(split_counts),
'heldout_MSE_home_intercept':float(errors[:,0].mean()),'heldout_MSE_ridge':float(errors[:,1].mean()),
'heldout_RMSE_home_intercept':float(np.sqrt(errors[:,0].mean())),'heldout_RMSE_ridge':float(np.sqrt(errors[:,1].mean())),
'relative_MSE_reduction':float(1-errors[:,1].mean()/errors[:,0].mean()),
'paired_MSE_difference_ridge_minus_intercept':float(difference.mean()),
'game_bootstrap_percentile95_diagnostic':list(map(float,np.quantile(boot,[.025,.975]))),
'bootstrap_limit':'Resamples games conditional on fitted models; does not resolve repeated-team/time dependence or supply guaranteed coverage. No causal interpretation.',
'unseen_test_player_ids':sorted(test_players-set(coefs)),
'fit_player_count':len(coefs),'test_game_count':len(games),
'interpretation':'Conditioned on realized lineup exposures; not pregame lineup/minutes forecasts, offense/defense split, possession rating, replacement level or fantasy value.'}
assert np.isclose(out['heldout_MSE_ridge'],fit['models']['duration_adjusted_ridge']['test']['game_home_margin_MSE'])
(p/'real-paired-evaluation.json').write_text(json.dumps(out,indent=2)+'\n')
with (p/'real-heldout-game-predictions.csv').open('w') as f:
 w=csv.writer(f);w.writerow(['game_id','actual_home_margin','intercept_prediction','ridge_prediction']);w.writerows((g,v['actual'],v['home_intercept_only'],v['duration_adjusted_ridge']) for g,v in sorted(games.items()))
with (p/'real-net-rate-estimates.csv').open('w') as f:
 w=csv.writer(f);w.writerow(['player_id','model_net_points_per48_relative_ridge_zero','training_seconds','training_games','reference_kind']);w.writerows((x,coefs[x],training_seconds[x],len(training_games[x]),'ridge-centered reference, not empirical replacement') for x in sorted(coefs))
print(json.dumps(out,indent=2))
