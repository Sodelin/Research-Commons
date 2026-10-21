"""Separate net-points-per48 ridge diagnostic; NOT the possession interaction model."""
import argparse,json,hashlib
from collections import defaultdict
from pathlib import Path
import numpy as np
from scipy import sparse
from scipy.sparse.linalg import lsqr
from duration_net_adapter import integrate_game

def design(rows,players):
 idx={p:i+1 for i,p in enumerate(players)};rr=[];cc=[];vv=[];unknown=0
 for i,r in enumerate(rows):
  cells={0:1.}
  for p in r['home_lineup']:
   if p in idx:cells[idx[p]]=cells.get(idx[p],0)+1.
   else:unknown+=1
  for p,secs in r['opponent_player_seconds'].items():
   if p in idx:cells[idx[p]]=cells.get(idx[p],0)-secs/r['seconds']
   else:unknown+=1
  for j,v in cells.items():rr.append(i);cc.append(j);vv.append(v)
 return sparse.csr_matrix((vv,(rr,cc)),shape=(len(rows),len(players)+1)),unknown

def fit(rows,lam,adjusted):
 players=sorted({p for r in rows for p in r['home_lineup']+list(r['opponent_player_seconds'])}) if adjusted else []
 X,_=design(rows,players);w=np.array([r['seconds']/2880 for r in rows]);y=np.array([r['home_net_points_per48'] for r in rows])
 penalty=np.r_[0.,np.full(len(players),lam)]
 A=sparse.vstack([X.multiply(np.sqrt(w)[:,None]),sparse.diags(np.sqrt(penalty))])
 sol=lsqr(A,np.r_[y*np.sqrt(w),np.zeros(len(players)+1)],atol=1e-10,btol=1e-10,iter_lim=max(1000,4*(len(players)+1)))
 if sol[1] not in (0,1,2,4,5):raise ValueError('ridge did not converge')
 return players,sol[0]

def score(rows,pred):
 games=defaultdict(lambda:np.zeros(3))
 for r,p in zip(rows,pred):games[r['game_id']]+=np.array([r['observed_home_pm'],p*r['seconds']/2880,r['seconds']/2880])
 return {'game_home_margin_MSE':float(np.mean([(a-b)**2 for a,b,t in games.values()])),
         'game_net_per48_MSE':float(np.mean([((a-b)/t)**2 for a,b,t in games.values()])),
         'games':len(games)}

def run(data,train_end,validation_end):
 if data['provenance']['kind']!='implementation_fixture':
  gate=data['provenance'].get('source_label_validation',{})
  if gate.get('status')!='passed' or not gate.get('evidence'):
   raise ValueError('REAL FIT BLOCKED: independent source-label validation required; internal complementary totals are insufficient')
 if train_end>=validation_end:raise ValueError('cutoffs must increase')
 rows=[];seen=set()
 for g in data['games']:
  if g['game_id'] in seen:raise ValueError('duplicate game')
  seen.add(g['game_id'])
  if not g.get('date') or not g.get('season'):raise ValueError('date and source league season required')
  rs=integrate_game(g['segments'],g['home_margin'])
  if any(r['game_id']!=g['game_id'] for r in rs):raise ValueError('game identity mismatch')
  rows.extend({**r,'date':g['date'],'season':g['season']} for r in rs)
 tr=[r for r in rows if r['date']<=train_end];va=[r for r in rows if train_end<r['date']<=validation_end];te=[r for r in rows if r['date']>validation_end]
 if not all((tr,va,te)):raise ValueError('empty chronological partition')
 report={'status':'Implementation fixture only' if data['provenance']['kind']=='implementation_fixture' else 'Real derived net-rate diagnostic; verify provenance',
         'target':'observed home margin / net points per48, NOT offense/defense or per100 possessions',
         'audit_games':len(seen),'rows_original_home_segments':len(rows),'models':{}}
 for name,adjusted in [('home_intercept_only',False),('duration_adjusted_ridge',True)]:
  candidates=[]
  for lam in ((1.,10.,100.) if adjusted else (1.,)):
   players,b=fit(tr,lam,adjusted);X,_=design(va,players);candidates.append((score(va,X@b)['game_home_margin_MSE'],lam))
  _,lam=min(candidates);players,b=fit(tr+va,lam,adjusted);X,unknown=design(te,players)
  report['models'][name]={'lambda':lam,'validation_candidates':candidates,'test':score(te,X@b),
                         'home_intercept_per48':float(b[0]),'player_coefficients_per48':dict(zip(players,map(float,b[1:]))),
                         'unseen_player_occurrences':unknown if adjusted else None}
 report['limits']=['Separate target, not validation of the possession interaction proposal','No possession count inferred',
   'No offense/defense split identified','Original home-segment outcomes only; no duplicated away targets',
   'Exact source durations/order/home labels must be verified externally','No uncertainty calibration or causal identification',
   'No recency, injury or transfer effects estimated','No superiority claim from implementation fixtures']
 return report

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('dataset',type=Path);ap.add_argument('--train-end',required=True);ap.add_argument('--validation-end',required=True);ap.add_argument('--out',required=True,type=Path);ap.add_argument('--permitted-real-data',action='store_true');a=ap.parse_args()
 d=json.loads(a.dataset.read_text());p=d['provenance']
 if p['kind']!='implementation_fixture' and (not a.permitted_real_data or not p.get('permission_basis') or not p.get('source')):raise ValueError('permitted source and explicit provenance required')
 result=run(d,a.train_end,a.validation_end);result['input_sha256']=hashlib.sha256(a.dataset.read_bytes()).hexdigest();result['provenance']=p
 a.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
