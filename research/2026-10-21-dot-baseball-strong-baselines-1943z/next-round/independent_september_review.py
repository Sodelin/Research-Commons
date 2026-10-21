"""Independent fitting/baseline/score verification from frozen saved design."""
from pathlib import Path
import csv,json
import numpy as np
p=Path(__file__).parent;z=np.load(p/'september-inputs.npz');r=json.loads((p/'SEPTEMBER-RESULTS.json').read_text());meta=json.loads((p/'september-cohort-local.json').read_text());stored=list(csv.DictReader(open(p/'september-predictions-local.csv')))
X,Y,H,R,E,yr,mo,role,f,q=[z[k] for k in ['X','Y','H','R','E','years','months','roles','f','q']]
tr=yr<=2023;va=(yr==2024)&(mo==9);fu=yr<=2024;te=yr==2025;sc=[2,3,5];ec=[0,1,4]
assert len(set(x['id'] for x in meta if x['year']==2025))==sum(te)
assert np.all(mo[te]==9) and not np.any(tr&va) and not np.any(fu&te)
def fit(mask,target,pen,j):
 m=np.mean(X[mask],axis=0);s=np.std(X[mask],axis=0);s[s<1e-12]=1
 A=np.c_[np.ones(sum(mask)),(X[mask]-m)/s];T=np.c_[np.ones(sum(target)),(X[target]-m)/s];D=np.sqrt(pen)*np.eye(A.shape[1]);D[0,0]=0
 return T@np.linalg.lstsq(np.r_[A,D],np.r_[Y[mask,j],np.zeros(A.shape[1])],rcond=None)[0]
def baseline(mask,target,option,j):
 if option=='zero':return np.zeros(sum(target))
 if option=='persistence':return R[target,sc[j]]*f[target]
 lam=float(option);ret=[]
 for idx in np.flatnonzero(target):
  grp=mask&(role==role[idx]);ex=(R[grp,ec[j]]*f[grp]).sum();factor=E[grp,j].sum()/ex if ex>0 else 1
  den=H[idx,ec[j]]+lam;rate=(H[idx,sc[j]]+lam*q[j])/den if den>0 else q[j]
  ret.append(rate*R[idx,ec[j]]*f[idx]*max(0,factor))
 return np.array(ret)
output={};pall=[];ball=[]
for j,name in enumerate(['batting','steal_only','simplified_pitching']):
 scores={a:np.mean(abs(fit(tr,va,a,j)-Y[va,j])) for a in [.1,1,10,100,1000]};alpha=min(scores,key=scores.get);assert alpha==r[name]['alpha']
 opts=['zero','persistence']+[str(a) for a in ([0,50,200,600] if j<2 else [0,30,90,270])]
 bs={o:np.mean(abs(baseline(tr,va,o,j)-Y[va,j])) for o in opts};sel=min(bs,key=bs.get);assert sel==r[name]['selected_baseline']
 pp=fit(fu,te,alpha,j);bb=baseline(fu,te,sel,j);pall.append(pp);ball.append(bb)
 gap=max(abs(pp-np.array([float(v['ridge_'+str(j)]) for v in stored])));bgap=max(abs(bb-np.array([float(v['baseline_'+str(j)]) for v in stored])))
 assert gap<1e-8 and bgap<1e-10
 output[name]={'alpha':alpha,'selected_baseline':sel,'prediction_gap':float(gap),'baseline_gap':float(bgap)}
pp=np.array(pall).sum(0);bb=np.array(ball).sum(0);truth=Y[te].sum(1);mae=float(abs(pp-truth).mean());bmae=float(abs(bb-truth).mean());assert abs(mae-r['supported_subtotal']['ridge']['MAE'])<1e-9
assert abs(bmae-r['supported_subtotal']['selected_baseline']['MAE'])<1e-9
print(json.dumps({'status':'PASS independent augmented-lstsq and rate-baseline refit, saved design only','n':int(sum(te)),'components':output,'subtotal_MAE':mae,'baseline_MAE':bmae,'original_claim_gate':r['supported_subtotal']['passes_gate']},indent=2))
