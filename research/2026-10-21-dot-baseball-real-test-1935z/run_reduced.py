import csv,io,json,zipfile,datetime as dt,collections,hashlib
from pathlib import Path
import numpy as np
p=Path(__file__).parent
F=['pa','ab','single','double','triple','hr','sh','sf','hbp','walk','k','xi','iw']
# internal vector PA,D,W,K,uBB,LPA,RPA
records=collections.defaultdict(list); audits=[]; pri=np.zeros((2,5))
for yr in range(2020,2026):
 z=zipfile.ZipFile(p/f'{yr}csvs.zip'); a=collections.defaultdict(lambda:np.zeros(7)); sums=collections.defaultdict(lambda:np.zeros(13)); status=collections.Counter();bad=0; seen=set()
 with z.open(f'{yr}plays.csv') as f:
  for r in csv.DictReader(io.TextIOWrapper(f)):
   status[(r['gametype'],r['pbp'])]+=1
   if r['gametype']!='regular' or r['pa']!='1':continue
   assert r['pbp']=='full',r['pbp']
   key=(r['gid'],r['pn']);assert key not in seen,('duplicate PA',key);seen.add(key)
   v=np.array([int(r[k]) for k in F]);pa,ab,si,do,tr,hr,sh,sf,hbp,walk,k,xi,iw=v
   den=ab+walk-iw+hbp+sf
   assert den==pa-iw-sh-xi,(yr,r['gid'],r['event'],v.tolist())
   w=.699*(walk-iw)+.728*hbp+.883*si+1.238*do+1.558*tr+1.979*hr
   assert r['pithand'] in ['L','R'],r['pithand']
   h=int(r['pithand']=='R');date=dt.datetime.strptime(r['date'],'%Y%m%d').date().toordinal()
   a[(r['batter'],date,h)]+=np.array([pa,den,w,k,walk-iw,pa*(1-h),pa*h]);sums[(r['gid'],r['batter'])]+=v
   if yr==2020:pri[h]+=np.array([pa,den,w,k,walk-iw])
 # Independent batting file verifies event totals, date of suspension deliberately not part of key.
 bs=collections.defaultdict(lambda:np.zeros(13))
 with z.open(f'{yr}batting.csv') as f:
  for r in csv.DictReader(io.TextIOWrapper(f)):
   if r['gametype']!='regular' or r['stattype']!='value':continue
   vals=[int(r['b_'+x]) for x in ['pa','ab','h','d','t','hr','sh','sf','hbp','w','k','xi','iw']]
   vals[2]-=sum(vals[3:6]);bs[(r['gid'],r['id'])]+=np.array(vals)
 dif=[(str(k),sums[k].tolist(),bs[k].tolist()) for k in set(sums)|set(bs) if not np.array_equal(sums[k],bs[k])]
 audits.append({'year':yr,'pa':int(sum(v[0] for v in a.values())),'game_player_reconciliation_differences':len(dif),'first_differences':dif[:5],'status':{str(k):v for k,v in status.items()}})
 for (b,d,h),v in a.items():records[b].append((d,h,*v))
 print('parsed',yr,audits[-1]['pa'],'reconcile',len(dif),flush=True)
(p/'panel-audit.json').write_text(json.dumps(audits,indent=2))
assert all(x['game_player_reconciliation_differences']==0 for x in audits),'Stop: independent totals do not reconcile'
# Reference prior fixed in2020, excludes later outcomes.
pi=pri[:,0]/pri[:,0].sum();q=pri[:,3:5]/pri[:,0,None];w0=pri[:,2].sum()/pri[:,1].sum()
rows=[];base=[];raw=[];std=[];targets=[]
for b,rr in sorted(records.items()):
 arr=np.array(rr); dates=arr[:,0];hands=arr[:,1];v=arr[:,2:]
 for year in range(2021,2026):
  for month in [5,7]:
   t=dt.date(year,month,1).toordinal();hist=(dates<t)&(dates>=t-365);rec=(dates<t)&(dates>=t-60);old=hist&~rec
   H=v[hist].sum(axis=0);R=v[rec].sum(axis=0)
   if H[0]<200 or R[0]<20:continue
   fut=(dates>=t)&(dates<t+60);T=v[fut].sum(axis=0);x=[]
   for days in [30,60,120,365]:x+=v[(dates<t)&(dates>=t-days)].sum(axis=0)[:2].tolist()
   for mask in [hist,rec]:
    u=v[mask].sum(axis=0);x += [(u[3]+50*np.sum(pi*q[:,0]))/(u[0]+50),(u[4]+50*np.sum(pi*q[:,1]))/(u[0]+50),(u[2]+50*w0)/(u[1]+50)]
   qs=[];mix=[]
   for mask in [hist,rec,old]:
    rates=[];counts=[]
    for h in [0,1]:
     u=v[mask&(hands==h)].sum(axis=0);counts.append(u[0]);rates.append((u[3:5]+50*q[h])/(u[0]+50))
    rates=np.array(rates);counts=np.array(counts);qs.append(rates);mix.append(counts/counts.sum() if counts.sum() else pi)
   x+=qs[0].ravel().tolist();x +=[mix[1][0],mix[2][0],min(365,t-int(dates[dates<t].max())),int(month==7)]
   dr=mix[1]@qs[1]-mix[2]@qs[2];ds=pi@(qs[1]-qs[2]);target=(T[2]-.320*T[1])/1.185
   rows.append(dict(batter=b,year=year,anchor=f'{year}-{month:02}-01',prior_pa=H[0],recent_pa=R[0],future_pa=T[0],future_D=T[1],future_W=T[2],target=target));base.append(x);raw.append(dr*R[1]);std.append(ds*R[1]);targets.append(target)
(p/'cohort-summary.json').write_text(json.dumps({'prior_hand_mix':pi.tolist(),'cohort_counts':dict(collections.Counter(str((r['year'],r['anchor'])) for r in rows)),'zero_future_pa':int(sum(r['future_pa']==0 for r in rows)),'n':len(rows)},indent=2))
# Freeze cohort/features locally before fit; raw derived records not public by default.
np.savez_compressed(p/'model-inputs.npz',base=base,raw=raw,std=std,y=targets)
(p/'cohort.json').write_text(json.dumps(rows))
y=np.array(targets);yr=np.array([r['year'] for r in rows]);B=np.array(base);designs={'baseline':B,'raw':np.column_stack([B,raw]),'standardized':np.column_stack([B,std])}
def fitpred(X,train,test,alpha):
 m=X[train].mean(0);s=X[train].std(0);s[s<1e-12]=1
 A=np.column_stack([np.ones(train.sum()),(X[train]-m)/s]);C=np.column_stack([np.ones(test.sum()),(X[test]-m)/s]);P=np.eye(A.shape[1])*alpha;P[0,0]=0
 return C@np.linalg.solve(A.T@A+P,A.T@y[train])
def stats(y,pred):
 return {'n':len(y),'MAE':float(np.abs(pred-y).mean()),'RMSE':float(np.sqrt(np.mean((pred-y)**2))),'bias':float((pred-y).mean()),'calibration_intercept_slope':np.linalg.lstsq(np.column_stack([np.ones(len(pred)),pred]),y,rcond=None)[0].tolist()}
out={};preds={};test=yr==2025
for name,X in designs.items():
 vals={str(a):float(np.abs(fitpred(X,yr<=2023,yr==2024,a)-y[yr==2024]).mean()) for a in [.1,1,10,100,1000]};alpha=float(min(vals,key=vals.get));pr=fitpred(X,yr<=2024,test,alpha);preds[name]=pr
 out[name]={'validation_MAE':vals,'chosen_alpha':alpha,'test':stats(y[test],pr),'by_anchor':{anchor:stats(y[test][np.array([r['anchor']==anchor for r in rows if r['year']==2025])],pr[np.array([r['anchor']==anchor for r in rows if r['year']==2025])]) for anchor in ['2025-05-01','2025-07-01']}}
# Paired player-cluster bootstrap on test only, no refitting.
d=np.abs(preds['raw']-y[test])-np.abs(preds['standardized']-y[test]);ids=np.array([r['batter'] for r in rows if r['year']==2025]);unique=np.unique(ids);rng=np.random.default_rng(20261021);vals=[]
for _ in range(1000):
 sample=rng.choice(unique,len(unique),replace=True); ix=np.concatenate([np.flatnonzero(ids==b) for b in sample]);vals.append(float(d[ix].mean()))
out['paired_gain']={'mean_raw_absolute_error_minus_standardized':float(d.mean()),'player_cluster_percentile95':np.quantile(vals,[.025,.975]).tolist(),'relative_MAE_gain':float(d.mean()/out['raw']['test']['MAE']),'bootstrap_replicates':1000}
(p/'RESULTS.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
with (p/'test-predictions.csv').open('w') as f:
 w=csv.writer(f);w.writerow(['batter','anchor','actual','baseline','raw','standardized'])
 for i,r in enumerate([r for r in rows if r['year']==2025]):w.writerow([r['batter'],r['anchor'],y[test][i],*[preds[n][i] for n in designs]])

# Reporting extension only: no feature or tuning change.
zero=np.array([r['future_pa']==0 for r in rows if r['year']==2025])
for name in designs:
 out[name]['zero_future_pa_test']=stats(y[test][zero],preds[name][zero]) if zero.any() else {'n':0,'metrics':None}
out['gate']={'relative_MAE_gain_vs_raw':out['paired_gain']['relative_MAE_gain'],'relative_MAE_gain_vs_baseline':1-out['standardized']['test']['MAE']/out['baseline']['test']['MAE'],'RMSE_ratio_vs_raw':out['standardized']['test']['RMSE']/out['raw']['test']['RMSE'],'passes_declared_raw_gate':bool(out['paired_gain']['relative_MAE_gain']>=.01 and out['paired_gain']['player_cluster_percentile95'][0]>0 and out['standardized']['test']['RMSE']<=1.02*out['raw']['test']['RMSE'])}
(p/'RESULTS.json').write_text(json.dumps(out,indent=2))
