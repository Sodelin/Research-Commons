"""Posthoc reporting and uncertainty diagnostics, no forecast changes."""
import sys,csv,json,io,zipfile
from pathlib import Path
import numpy as np
p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).parent;z=np.load(p/'september-inputs.npz');Y=z['Y'];H=z['H'];R=z['R'];E=z['E'];years=z['years'];months=z['months'];roles=z['roles'];f=z['f'];q=z['q'];meta=json.loads((p/'september-cohort-local.json').read_text());res=json.loads((p/'SEPTEMBER-RESULTS.json').read_text());train=years<=2023;val=(years==2024)&(months==9);full=years<=2024;test=years==2025;sc=[2,3,5];ec=[0,1,4]
def baseline(tr,te,name,j):
 if name=='zero':return np.zeros(te.sum())
 if name=='persistence':return R[te,sc[j]]*f[te]
 c=float(name);ex=R[te,ec[j]]*f[te];rs=roles[te]
 for role in set(rs):
  ix=tr&(roles==role);den=np.sum(R[ix,ec[j]]*f[ix]);factor=E[ix,j].sum()/den if den>0 else 1;ex[rs==role]*=max(0,factor)
 den=H[te,ec[j]]+c;rate=np.full(te.sum(),q[j]);np.divide(H[te,sc[j]]+c*q[j],den,out=rate,where=den>0);return ex*rate
names=['batting','steal_only','simplified_pitching'];pv=np.column_stack([baseline(train,val,res[name]['selected_baseline'],j) for j,name in enumerate(names)]);pt=np.column_stack([baseline(full,test,res[name]['selected_baseline'],j) for j,name in enumerate(names)]);rv=Y[val].sum(1)-pv.sum(1);rt=roles[test];bands={};lower=np.zeros(test.sum());upper=lower.copy()
for role in sorted(set(rt)):
 mask=roles[val]==role;fallback=mask.sum()<20;sample=rv if fallback else rv[mask];lo,hi=np.quantile(sample,[.05,.95]);maskt=rt==role;lower[maskt]=pt.sum(1)[maskt]+lo;upper[maskt]=pt.sum(1)[maskt]+hi
 bands[role]=dict(validation_role_n=int(mask.sum()),calibration_n=len(sample),pooled_fallback=bool(fallback),residual_p05=float(lo),residual_p95=float(hi),test_n=int(maskt.sum()))
y=Y[test].sum(1);covered=(y>=lower)&(y<=upper)
for role in bands:bands[role]['test_coverage']=float(covered[rt==role].mean())
out=dict(method='posthoc diagnostic 5th/95th percentiles of September2024 selected-baseline subtotal residuals; not conformal, not guaranteed90%coverage',quantile_method='numpy.quantile linear interpolation',selection_coupled_calibration=True,forecast_unchanged=True,overall_test_coverage=float(covered.mean()),mean_band_width=float((upper-lower).mean()),median_band_width=float(np.median(upper-lower)),by_role=bands)
(p/'UNCERTAINTY-DIAGNOSTIC.json').write_text(json.dumps(out,indent=2))
players={}
with zipfile.ZipFile(p.parent/'2025csvs.zip') as zi:
 for row in csv.DictReader(io.TextIOWrapper(zi.open('2025allplayers.csv'))):players[row['id']]=row['first']+' '+row['last']
with (p/'selected-baseline-report-local.csv').open('w') as fh:
 w=csv.writer(fh);w.writerow(['player_id','name','role','window_start','window_end_exclusive','forecast_batting_proxy','forecast_steal_only','forecast_pitching_proxy','supported_subtotal','diagnostic_lower','diagnostic_upper','actual_supported_subtotal','complete_value','missing_or_partial'])
 for i,r in enumerate([r for r in meta if r['year']==2025]):w.writerow([r['id'],players.get(r['id'],r['id']),r['role'],'2025-09-01','2025-10-31',*pt[i],pt[i].sum(),lower[i],upper[i],y[i],'unavailable','full fielding; full advancement; position; park/league; replacement; full pitching allocation'])
print(json.dumps(out,indent=2))
