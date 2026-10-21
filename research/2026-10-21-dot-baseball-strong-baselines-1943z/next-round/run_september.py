"""Frozen season-end follow-up. Run only after prerefit review."""
import json,datetime as dt,collections,csv
from pathlib import Path
import numpy as np
p=Path(__file__).parent
players=json.loads((p/'daily-supported-local.json').read_text())
end={2021:'2021-10-03',2022:'2022-10-05',2023:'2023-10-01',2024:'2024-09-29',2025:'2025-09-28'}
X=[];Y=[];HIST=[];REC=[];E=[];meta=[];ref=np.zeros(7)
for b,rr in sorted(players.items()):
 a=np.array(rr);dates=a[:,0];v=a[:,1:];ref+=v[(dates>=dt.date(2020,1,1).toordinal())&(dates<dt.date(2021,1,1).toordinal())].sum(0)
 for year in range(2021,2026):
  for month in [5,7,9]:
   if year==2025 and month!=9:continue
   t=dt.date(year,month,1).toordinal();H=v[(dates<t)&(dates>=t-365)].sum(0);R=v[(dates<t)&(dates>=t-60)].sum(0)
   bat=H[0]>=200 and R[0]>=20;pit=H[4]>=90 and R[4]>=15
   if not (bat or pit):continue
   f=max(0,min(60,dt.date.fromisoformat(end[year]).toordinal()-t+1))/60
   x=[]
   for days in [30,60,120,365]:x+=v[(dates<t)&(dates>=t-days)].sum(0)[:6].tolist()
   x=x+[z*f for z in x]+[int(month==7),int(month==9),f,int(bat),int(pit)]
   T=v[(dates>=t)&(dates<t+60)].sum(0);X.append(x);Y.append(T[[2,3,5]]);HIST.append(H);REC.append(R);E.append(T[[0,1,4]]);meta.append(dict(id=b,year=year,month=month,role='two-way' if bat and pit else 'batting' if bat else 'pitching',fraction=f))
X=np.array(X);Y=np.array(Y);H=np.array(HIST);R=np.array(REC);E=np.array(E);years=np.array([r['year'] for r in meta]);months=np.array([r['month'] for r in meta]);roles=np.array([r['role'] for r in meta]);f=np.array([r['fraction'] for r in meta]);sc=[2,3,5];ec=[0,1,4];q=ref[sc]/ref[ec]
train=years<=2023;val=(years==2024)&(months==9);full=years<=2024;test=years==2025
assert train.any() and val.any() and full.any() and test.any()
assert not (train & val).any() and not (full & test).any()
assert len({r['id'] for r in meta if r['year']==2025})==int(test.sum())
assert all(np.isfinite(a).all() for a in [X,Y,H,R,E,f,q])
assert all(dt.date(r['year'],r['month'],1)+dt.timedelta(days=59)<dt.date(r['year']+1,1,1) for r in meta)
np.savez_compressed(p/'september-inputs.npz',X=X,Y=Y,H=H,R=R,E=E,years=years,months=months,roles=roles,f=f,q=q)
(p/'september-cohort-local.json').write_text(json.dumps(meta))
def ridge(tr,te,a,j):
 m=X[tr].mean(0);s=X[tr].std(0);s[s<1e-12]=1;A=np.column_stack([np.ones(tr.sum()),(X[tr]-m)/s]);B=np.column_stack([np.ones(te.sum()),(X[te]-m)/s]);D=np.eye(A.shape[1])*a;D[0,0]=0
 return B@np.linalg.solve(A.T@A+D,A.T@Y[tr,j])
def base(tr,te,name,j):
 if name=='zero':return np.zeros(te.sum())
 if name=='persistence':return R[te,sc[j]]*f[te]
 c=float(name);ex=R[te,ec[j]]*f[te];rs=roles[te]
 for role in set(rs):
  ix=tr&(roles==role);den=np.sum(R[ix,ec[j]]*f[ix]);factor=np.sum(E[ix,j])/den if den>0 else 1.
  ex[rs==role]*=max(0,factor)
 den=H[te,ec[j]]+c;rate=np.full(te.sum(),q[j]);np.divide(H[te,sc[j]]+c*q[j],den,out=rate,where=den>0)
 return ex*rate

def metrics(y,pred):
 return dict(n=len(y),MAE=float(abs(y-pred).mean()),RMSE=float(np.sqrt(((y-pred)**2).mean())),bias=float((pred-y).mean()),calibration=np.linalg.lstsq(np.column_stack([np.ones(len(pred)),pred]),y,rcond=None)[0].tolist() if np.std(pred)>1e-12 and np.std(y)>1e-12 else None)
out={'scope':'previously unscored retrospective season-end supported-score follow-up; not full value','counts':dict(collections.Counter(str((r['year'],r['month'],r['role'])) for r in meta)),'calendar_end':end};preds=[];bps=[]
for j,name in enumerate(['batting','steal_only','simplified_pitching']):
 vals={str(a):float(abs(ridge(train,val,a,j)-Y[val,j]).mean()) for a in [.1,1,10,100,1000]};alpha=float(min(vals,key=vals.get));pred=ridge(full,test,alpha,j)
 grid=['zero','persistence']+[str(c) for c in ([0,50,200,600] if j<2 else [0,30,90,270])];bv={k:float(abs(base(train,val,k,j)-Y[val,j]).mean()) for k in grid};sel=min(bv,key=bv.get);bp=base(full,test,sel,j);preds.append(pred);bps.append(bp)
 out[name]=dict(alpha=alpha,validation_ridge=vals,validation_baselines=bv,selected_baseline=sel,ridge=metrics(Y[test,j],pred),baseline=metrics(Y[test,j],bp),by_role={role:dict(ridge=metrics(Y[test,j][roles[test]==role],pred[roles[test]==role]),baseline=metrics(Y[test,j][roles[test]==role],bp[roles[test]==role])) for role in sorted(set(roles[test]))},zero_exposure_count=int((E[test,j]==0).sum()),zero_exposure_nonzero_score=int(((E[test,j]==0)&(np.abs(Y[test,j])>1e-12)).sum()))
pr=np.array(preds).T;bp=np.array(bps).T;truth=Y[test].sum(1);d=abs(truth-bp.sum(1))-abs(truth-pr.sum(1));rng=np.random.default_rng(20261022);boot=[float(rng.choice(d,len(d),replace=True).mean()) for _ in range(1000)];ci=np.quantile(boot,[.025,.975]).tolist();mr=metrics(truth,pr.sum(1));mb=metrics(truth,bp.sum(1));gain=1-mr['MAE']/mb['MAE']
out['supported_subtotal']=dict(ridge=mr,selected_baseline=mb,relative_MAE_gain=gain,paired_player_bootstrap95=ci,passes_gate=bool(gain>=.01 and ci[0]>0 and mr['RMSE']<=1.02*mb['RMSE']))
(p/'SEPTEMBER-RESULTS.json').write_text(json.dumps(out,indent=2))
with (p/'september-predictions-local.csv').open('w') as fh:
 w=csv.writer(fh);w.writerow(['id','role',*[f'actual_{j}' for j in range(3)],*[f'ridge_{j}' for j in range(3)],*[f'baseline_{j}' for j in range(3)]])
 for i,r in enumerate([r for r in meta if r['year']==2025]):w.writerow([r['id'],r['role'],*Y[test][i],*pr[i],*bp[i]])
print(json.dumps(out,indent=2))
