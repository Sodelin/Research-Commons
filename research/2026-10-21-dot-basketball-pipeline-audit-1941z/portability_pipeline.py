"""Dataset-agnostic, exposure-conditioned offensive scoring pilot.
No download routines. A provenance declaration is an audit input, not a license.
"""
import argparse, bisect, csv, hashlib, json
from collections import defaultdict
from datetime import date
from pathlib import Path
import numpy as np
from scipy import sparse
from scipy.sparse.linalg import lsqr

MODELS=('additive','common_context','player_interaction')

def number(x, name, integer=False):
    if isinstance(x,bool): raise ValueError(f'{name}: boolean is not numeric')
    v=float(x)
    if not np.isfinite(v) or (integer and v != int(v)): raise ValueError(f'{name}: invalid number')
    return v

def audit(rows, games, history):
    """Strict complete-game score checks, not proof of correct event reconstruction."""
    if not rows or not games: raise ValueError('empty rows/games')
    gm={};seen=set();totals=defaultdict(float);teams_seen=defaultdict(set);player_teams={}
    for g in games:
        if g['game_id'] in gm: raise ValueError('duplicate game_id')
        date.fromisoformat(g['date'])
        if not isinstance(g.get('season'),str) or not g['season']:raise ValueError('explicit league season required')
        if g['home_team']==g['away_team']: raise ValueError('same game teams')
        for k in ('home_points','away_points'):
            if number(g[k],k,True)<0: raise ValueError('negative score')
        gm[g['game_id']]=g
    for r in rows:
        key=(r['game_id'],r['stint_id'])
        if key in seen: raise ValueError('duplicate game/stint')
        seen.add(key)
        if r['game_id'] not in gm: raise ValueError('missing game manifest')
        g=gm[r['game_id']]
        if r['date']!=g['date']: raise ValueError('game date mismatch')
        if r.get('season')!=g['season']:raise ValueError('explicit league season mismatch')
        off,defn=r['offense'],r['defense']
        if len(off)!=5 or len(defn)!=5 or len(set(off+defn))!=10: raise ValueError('need ten distinct lineup IDs')
        if not all(isinstance(p,str) and p for p in off+defn): raise ValueError('invalid player ID')
        if {r['off_team'],r['def_team']}!={g['home_team'],g['away_team']}: raise ValueError('team mismatch')
        for side,team in [('offense',r['off_team']),('defense',r['def_team'])]:
            for p in r[side]:
                key=(r['game_id'],p)
                if key in player_teams and player_teams[key]!=team:raise ValueError('player changes teams within game')
                player_teams[key]=team
        if number(r['possessions'],'possessions',True)<=0: raise ValueError('nonpositive possessions; reconcile zero-possession events upstream')
        if number(r['points'],'points',True)<0: raise ValueError('negative points')
        if number(r['home'],'home',True)!=int(r['off_team']==g['home_team']): raise ValueError('home flag mismatch')
        if number(r['period'],'period',True)<1: raise ValueError('invalid period')
        number(r['score_margin'],'score_margin',True)
        totals[(r['game_id'],r['off_team'])]+=r['points'];teams_seen[r['game_id']].add(r['off_team'])
    for gid,g in gm.items():
        if teams_seen[gid]!={g['home_team'],g['away_team']}: raise ValueError('missing team possessions')
        for team,score in [(g['home_team'],g['home_points']),(g['away_team'],g['away_points'])]:
            if totals[gid,team]!=score: raise ValueError('score reconciliation failed')
    hseen=set()
    for h in history:
        date.fromisoformat(h['date'])
        key=(h['game_id'],h['player_id'])
        if key in hseen: raise ValueError('duplicate player-game history')
        hseen.add(key)
        a=number(h['three_pa'],'three_pa',True);b=number(h['fga'],'fga',True)
        if a<0 or b<a: raise ValueError('invalid attempt history')
    return {'games':len(gm),'rows':len(rows),'score_reconciled':True,
            'lineup_ID_cardinality_checked':True,'event_lineup_reconstruction_verified':False}

class History:
    def __init__(self, rows, prior=.35, prior_attempts=50.):
        self.prior=prior;self.prior_attempts=prior_attempts;self.data={}
        grouped=defaultdict(list)
        for r in rows: grouped[r['player_id']].append(r)
        for p,rs in grouped.items():
            rs=sorted(rs,key=lambda r:r['date'])
            self.data[p]=([r['date'] for r in rs],np.cumsum([0]+[r['three_pa'] for r in rs]),np.cumsum([0]+[r['fga'] for r in rs]))
    def rate(self,p,before):
        if p not in self.data: return self.prior
        dates,a,b=self.data[p];n=bisect.bisect_left(dates,before)
        return float((a[n]+self.prior_attempts*self.prior)/(b[n]+self.prior_attempts))
    def contexts(self,r,before):
        rates=np.array([self.rate(p,before) for p in r['offense']])
        return (rates.sum()-rates)/4

def cut_after(d):
    return date.fromordinal(date.fromisoformat(d).toordinal()+1).isoformat()

def contexts(rows,h,frozen_before=None):
    # Each training row excludes its own entire game date. Frozen forecasts
    # use a fixed past snapshot even if earlier evaluation games are available.
    return [h.contexts(r,min(r['date'],frozen_before) if frozen_before else r['date']) for r in rows]

class Design:
    def __init__(self, rows, ctx, model):
        self.model=model
        self.players=sorted({p for r in rows for p in r['offense']+r['defense']})
        self.index={p:i for i,p in enumerate(self.players)};self.P=len(self.players)
        self.seasons=sorted({r['season'] for r in rows})
        self.season_index={s:i for i,s in enumerate(self.seasons[1:])}
        self.base=4+len(self.season_index)
        w=np.array([r['possessions'] for r in rows],float)
        self.center=float(np.average([np.mean(c) for c in ctx],weights=w))
        self.dim=self.base+2*self.P+(1 if model!='additive' else 0)+(self.P if model=='player_interaction' else 0)
    def matrix(self,rows,ctx):
        rr=[];cc=[];vv=[];unknown=[]
        for i,(r,c) in enumerate(zip(rows,ctx)):
            cells={0:1.,1:float(r['home']),2:float(r['period'])/4,3:float(r['score_margin'])/20}
            season=r['season']
            if season in self.season_index: cells[4+self.season_index[season]]=1.
            unk=0
            for side,key in enumerate(('offense','defense')):
                for p in r[key]:
                    if p in self.index: cells[self.base+side*self.P+self.index[p]]=1.
                    else: unk+=1
            start=self.base+2*self.P
            if self.model!='additive': cells[start]=float(np.mean(c)-self.center)
            if self.model=='player_interaction':
                for p,value in zip(r['offense'],c):
                    if p in self.index: cells[start+1+self.index[p]]=float(value-self.center)
            for j,v in cells.items():rr.append(i);cc.append(j);vv.append(v)
            unknown.append(unk)
        return sparse.csr_matrix((vv,(rr,cc)),shape=(len(rows),self.dim)),unknown
    def penalties(self,lam,mult):
        # Only intercept unpenalized. Context covariates lightly regularized;
        # player, season and interaction choices remain explicit, inspectable.
        v=np.full(self.dim,lam);v[:self.base]=1e-6;v[0]=0.
        if self.model!='additive':v[self.base+2*self.P]=lam
        if self.model=='player_interaction':v[-self.P:]=lam*mult
        return v

def fit(rows,ctx,model,lam,mult):
    d=Design(rows,ctx,model);X,_=d.matrix(rows,ctx)
    w=np.array([r['possessions'] for r in rows],float)
    y=np.array([r['points']/r['possessions'] for r in rows])
    A=sparse.vstack([X.multiply(np.sqrt(w)[:,None]),sparse.diags(np.sqrt(d.penalties(lam,mult)))],format='csr')
    b=np.r_[y*np.sqrt(w),np.zeros(d.dim)]
    sol=lsqr(A,b,atol=1e-10,btol=1e-10,iter_lim=max(1000,4*d.dim))
    if sol[1] not in (0,1,2,4,5):raise ValueError(f'LSQR did not converge: {sol[1]}')
    return d,sol[0],{'lsqr_stop':int(sol[1]),'iterations':int(sol[2]),'columns':d.dim,'rows':len(rows)}

def game_loss(rows,pred):
    agg=defaultdict(lambda:np.zeros(3))
    for r,p in zip(rows,pred):agg[(r['game_id'],r['off_team'])]+=np.array([r['points'],p*r['possessions'],r['possessions']])
    return float(sum(n*((y-p)/n)**2 for y,p,n in agg.values())/sum(v[2] for v in agg.values()))

def net_game_loss(rows,pred):
    agg=defaultdict(lambda:np.zeros((2,3)))
    for r,p in zip(rows,pred):agg[r['game_id']][0 if r['home'] else 1]+=np.array([r['points'],p*r['possessions'],r['possessions']])
    losses=[];weights=[]
    for a in agg.values():
        if np.any(a[:,2]<=0):raise ValueError('net game evaluation missing side')
        actual=a[0,0]/a[0,2]-a[1,0]/a[1,2]
        predicted=a[0,1]/a[0,2]-a[1,1]/a[1,2]
        losses.append((actual-predicted)**2);weights.append(a[:,2].mean())
    return float(np.average(losses,weights=weights))

def support(train,trainctx,test,testctx,unknown):
    store=defaultdict(list)
    for r,c in zip(train,trainctx):
        for p,v in zip(r['offense'],c):store[p].append((float(v),r['game_id']))
    output=[]
    for r,c,unk in zip(test,testctx,unknown):
        reasons=[];details=[]
        if unk:reasons.append('unseen_player')
        for p,v in zip(r['offense'],c):
            vals=store[p]
            if not vals:lo=hi=None;near=0
            else:
                lo,hi=map(float,np.quantile([x[0] for x in vals],[.05,.95]))
                near=len({g for z,g in vals if abs(z-v)<=.05})
            ok=lo is not None and lo<=v<=hi and near>=10
            if not ok:reasons.append('limited_marginal_context_support')
            details.append({'player':p,'nearby_games':near,'range05_95':[lo,hi],'target':float(v)})
        output.append({'flag':bool(reasons),'reasons':sorted(set(reasons)),'players':details})
    return output

def run(rows,games,history,train_end,validation_end,grid=(1.,10.,100.),interaction_multiplier=10.,data_kind='implementation_fixture',label_validation=None):
    if data_kind!='implementation_fixture':
        gate=label_validation or {}
        if gate.get('status')!='passed' or not gate.get('evidence'):raise ValueError('independent source-label validation required for real possession fit')
    if train_end>=validation_end:raise ValueError('cutoffs not increasing')
    report={'status':'IMPLEMENTATION TEST ONLY' if data_kind=='implementation_fixture' else 'REAL DATA FIT: provenance requires human verification',
            'audit':audit(rows,games,history),'estimand':'exposure-conditioned offensive points per possession',
            'cutoffs':{'train_end':train_end,'validation_end':validation_end},'models':{}}
    rows=sorted(rows,key=lambda r:(r['date'],r['game_id'],r['stint_id']))
    tr=[r for r in rows if r['date']<=train_end]
    va=[r for r in rows if train_end<r['date']<=validation_end]
    te=[r for r in rows if r['date']>validation_end]
    if not all((tr,va,te)):raise ValueError('empty chronological partition')
    if len({r['game_id'] for r in tr}&{r['game_id'] for r in va}) or len({r['game_id'] for r in va}&{r['game_id'] for r in te}):raise ValueError('game split leakage')
    h=History(history);tc=contexts(tr,h);vc=contexts(va,h,cut_after(train_end))
    final=tr+va;fc=contexts(final,h);ec=contexts(te,h,cut_after(validation_end))
    predictions=[]
    for model in MODELS:
        candidates=[]
        for lam in grid:
            d,b,meta=fit(tr,tc,model,lam,interaction_multiplier)
            X,_=d.matrix(va,vc);candidates.append((game_loss(va,X@b),lam))
        val_loss,lam=min(candidates)
        d,b,meta=fit(final,fc,model,lam,interaction_multiplier)
        X,unknown=d.matrix(te,ec);pred=np.asarray(X@b)
        flags=support(final,fc,te,ec,unknown)
        report['models'][model]={'selected_lambda':lam,'validation_loss':val_loss,'validation_grid':candidates,
                                'test_game_team_weighted_MSE':game_loss(te,pred),'test_net_game_rate_MSE':net_game_loss(te,pred),'numerics':meta,
                                'flagged_rows':sum(f['flag'] for f in flags),'test_rows':len(te),
                                'unseen_season_rows':sum(r['season'] not in d.seasons for r in te),
                                'context_center':d.center,
                                'common_context_coef':float(b[d.base+2*d.P]) if model!='additive' else 0.,
                                'player_coefficients':{p:{'a':float(b[d.base+i]),'b':float(b[d.base+d.P+i]),'u':float(b[-d.P+i]) if model=='player_interaction' else 0.,'rate':h.rate(p,cut_after(validation_end))} for p,i in d.index.items()},
                                'out_of_physical_range_predictions':int(np.sum((pred<0)|(pred>5)))}
        for r,p,f in zip(te,pred,flags):predictions.append({'model':model,'game_id':r['game_id'],'stint_id':r['stint_id'],
                'date':r['date'],'off_team':r['off_team'],'predicted_ppp':float(p),'actual_points':r['points'],
                'possessions':r['possessions'],'support':f})
    report['limits']=['No causal replacement identification','No confidence intervals or interval coverage claims',
                      'Support is a heuristic marginal diagnostic, not positivity certification',
                      'No real-data accuracy claim when running fixtures','All test rows scored regardless of support',
                      'No event-level substitution validation or automated source-license verification',
                      'No transfer-cohort tagging yet; requires verified transaction/eligibility data',
                      'No pregame minutes/lineup forecast; realized exposures conditioned upon',
                      'No game-cluster uncertainty estimation yet; losses are descriptive']
    return report,predictions

def main():
    ap=argparse.ArgumentParser();ap.add_argument('dataset',type=Path);ap.add_argument('--train-end',required=True);ap.add_argument('--validation-end',required=True);ap.add_argument('--out',required=True,type=Path);ap.add_argument('--permitted-real-data',action='store_true')
    args=ap.parse_args();data=json.loads(args.dataset.read_text());prov=data['provenance']
    if prov['kind']!='implementation_fixture':
        if not args.permitted_real_data or not prov.get('source') or not prov.get('permission_basis'):
            raise ValueError('real-data fit requires explicit permitted-data flag and provenance; these do not themselves verify rights')
    report,predictions=run(data['rows'],data['games'],data['history'],args.train_end,args.validation_end,data_kind=prov['kind'],label_validation=prov.get('source_label_validation'))
    report['provenance']=prov;report['input_sha256']=hashlib.sha256(args.dataset.read_bytes()).hexdigest()
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'audit-and-fit.json').write_text(json.dumps(report,indent=2)+'\n')
    (args.out/'predictions.json').write_text(json.dumps(predictions,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
