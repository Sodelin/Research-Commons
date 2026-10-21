"""Independent ridge refit via augmented least squares, not normal-equation solve."""
from pathlib import Path
import csv,json
import numpy as np
p=Path(__file__).parent
z=np.load(p/'model-inputs.npz');rows=json.loads((p/'cohort.json').read_text());result=json.loads((p/'RESULTS.json').read_text());pred=list(csv.DictReader(open(p/'test-predictions.csv')))
y=z['y'];years=np.array([r['year'] for r in rows]);out={}
assert len(set((r['batter'],r['anchor']) for r in rows))==len(rows)
assert all(r['prior_pa']>=200 and r['recent_pa']>=20 for r in rows)
assert all(r['target']==r['future_D']==r['future_W']==0 for r in rows if r['future_pa']==0)
for name,X in [('baseline',z['base']),('raw',np.column_stack((z['base'],z['raw']))),('standardized',np.column_stack((z['base'],z['std'])))]:
 def predict(tr,te,a):
  m=X[tr].mean(axis=0);s=X[tr].std(axis=0);s=np.where(s<1e-12,1,s)
  A=np.column_stack((np.ones(tr.sum()),(X[tr]-m)/s));T=np.column_stack((np.ones(te.sum()),(X[te]-m)/s))
  penalty=np.sqrt(a)*np.eye(A.shape[1]);penalty[0,0]=0
  coef=np.linalg.lstsq(np.vstack((A,penalty)),np.r_[y[tr],np.zeros(A.shape[1])],rcond=None)[0]
  return T@coef
 vals={a:float(np.mean(abs(predict(years<=2023,years==2024,a)-y[years==2024]))) for a in [.1,1,10,100,1000]}
 a=min(vals,key=vals.get);assert a==result[name]['chosen_alpha']
 prediction=predict(years<=2024,years==2025,a);stored=np.array([float(r[name]) for r in pred]);gap=float(max(abs(prediction-stored)))
 assert gap<1e-8,(name,gap)
 e=prediction-y[years==2025];mae=float(np.mean(abs(e)));rmse=float(np.sqrt(np.mean(e*e)))
 assert abs(mae-result[name]['test']['MAE'])<1e-9
 assert abs(rmse-result[name]['test']['RMSE'])<1e-9
 out[name]={'chosen_alpha':a,'max_prediction_difference':gap,'MAE':mae,'RMSE':rmse}
print(json.dumps({'status':'PASS independent augmented-lstsq refit of saved design, not independent raw parser','results':out,'test_rows':len(pred),'cohort_rows':len(rows),'eligibility_and_zero_exposure':'PASS'},indent=2))
