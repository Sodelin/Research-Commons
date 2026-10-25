"""Explicit changed-experiment synthetic MLE comparison, fixed nucleotide calls."""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from compare_locus_length_designs import PairLaw
rng=np.random.default_rng(202610251);truth=np.array([1.,2.,1.]);bounds=[(.5,1.5),(1.75,3),(.5,1.5)];B=60000000
rows=[];records=[]
for L in [3,12,64,128]:
 law=PairLaw(L);p,J=law(truth);p=p/p.sum();N=B//(2*L)
 def objective(z,obs):
  q,G=law(z);positive=obs>0
  return np.sum(obs[positive]*np.log(obs[positive]/q[positive])),-G.T@(obs/q)
 estimates=[];flags=0;edge=0
 for rep in range(60):
  counts=rng.multinomial(N,p);obs=counts/N;fits=[]
  for start in [[.75,2.4,.75],[1.25,2.7,1.25],[1.1,1.8,.8]]:
   fits.append(minimize(lambda z:objective(z,obs),start,jac=True,bounds=bounds,method='L-BFGS-B',options={'ftol':1e-15,'gtol':1e-10,'maxiter':600}))
  fit=min(fits,key=lambda r:r.fun);estimates.append(fit.x);flags+=not fit.success
  edge+=any(abs(fit.x[i]-lim)<1e-6 for i,b in enumerate(bounds) for lim in b)
  grad=objective(fit.x,obs)[1];pg=fit.x-np.clip(fit.x-grad,[v[0] for v in bounds],[v[1] for v in bounds])
  records.append({'L':L,'N':N,'rep':rep,'counts':counts.tolist(),'estimate':fit.x.tolist(),'optimizer_success':bool(fit.success),'projected_gradient_sup':float(max(abs(pg))),'objective':float(fit.fun)})
 err=np.array(estimates)-truth
 F=J.T@np.diag(1/p)@J
 rows.append({'L':L,'N':N,'nucleotide_calls':2*L*N,'replicates':60,'rmse':np.sqrt(np.mean(err**2,axis=0)).tolist(),'q90_abs_error':np.quantile(abs(err),.9,axis=0).tolist(),'all_error_below_0_1_count':int(np.sum(np.max(abs(err),axis=1)<.1)),'optimizer_failure_flags':flags,'boundary_fits':edge,'max_projected_gradient_sup':max(v['projected_gradient_sup'] for v in records if v['L']==L),'fisher_local_sd':np.sqrt(np.diag(np.linalg.inv(F))/N).tolist()})
out={'status':'executed fixed-call changed-experiment synthetic benchmark; no coverage or global-optimizer guarantee','optimizer_starts':[[.75,2.4,.75],[1.25,2.7,1.25],[1.1,1.8,.8]],'seed':202610251,'truth':truth.tolist(),'bounds':bounds,'fixed_nucleotide_budget':B,'rows':rows,'records':records}
Path(__file__).with_name('fixed-call-budget-nontruth-benchmark.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
