"""Seeded synthetic sufficient-statistic MLE diagnostics; floats, not certificates."""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
C=np.array([[27,-81,81,-27],[27,27,-135,81],[9,45,27,-81],[1,9,27,27]],float)/64
bounds=[(.5,1.5),(1.75,3.),(.5,1.5)]
def law(z):
 x,y,t=z;a=np.arange(1,4,dtype=float);e=np.exp(-(x+a)*t);d=y/(y+a)-x/(x+a)
 phi=x/(x+a)+d*e
 J=np.array([a/(x+a)**2*(1-e)-t*d*e,a/(y+a)**2*e,-(x+a)*d*e]).T
 return C@np.r_[1,phi], C[:,1:]@J
truth=np.array([1.,2.,1.]);p0,J0=law(truth)
F=J0.T@np.diag(1/p0)@J0
Finv=np.linalg.inv(F)
ev,U=np.linalg.eigh(F)
def obj(z,obs):
 p,J=law(z)
 if np.any(p<=0):return 1e100,np.zeros(3)
 # Constant centered deviance per locus improves stopping scale.
 f=np.sum(obs*np.log(obs/p),where=obs>0)
 g=-J.T@(obs/p)
 return f,g
def fit(obs):
 results=[]
 for start in [truth,[.9,2.5,.9],[1.1,1.8,1.2]]:
  r=minimize(lambda z:obj(z,obs),start,jac=True,bounds=bounds,method='L-BFGS-B',options={'ftol':1e-15,'gtol':1e-11,'maxiter':600})
  results.append(r)
 return min(results,key=lambda r:r.fun)
# Fix the tail hazard at 2.2, then select nuisance coordinates by KL proximity.
def rivalobj(v):
 f,g=obj([v[0],2.2,v[1]],p0);return f,g[[0,2]]
rival=minimize(rivalobj,[1.,1.],jac=True,bounds=[bounds[0],bounds[2]],method='L-BFGS-B',options={'ftol':1e-16,'gtol':1e-13,'maxiter':1000})
z1=np.array([rival.x[0],2.2,rival.x[1]])
p1,_=law(z1)
chi=np.sum((p1-p0)**2/p0)
# Rational rounded candidate becomes the independently certified pair.
z1_rounded=[f'{z1[0]:.10f}','2.2',f'{z1[2]:.10f}']
rng=np.random.default_rng(20261025)
rows=[]; records=[]
for N in [10000,100000,1000000,10000000]:
 estimates=[];fail=0;edge=0
 for rep in range(60):
  counts=rng.multinomial(N,p0);r=fit(counts/N)
  estimates.append(r.x);fail+=not r.success
  edge+=any(abs(r.x[i]-lim)<1e-6 for i,b in enumerate(bounds) for lim in b)
  gradient=obj(r.x,counts/N)[1]
  projected_gradient=r.x-np.clip(r.x-gradient,[b[0] for b in bounds],[b[1] for b in bounds])
  records.append({'projected_gradient_sup':float(max(abs(projected_gradient))),'N':N,'rep':rep,'counts':counts.tolist(),'estimate':r.x.tolist(),'objective':float(r.fun),'optimizer_success':bool(r.success)})
 estimates=np.array(estimates);err=estimates-truth
 rows.append({'N':N,'replicates':60,'rmse':np.sqrt(np.mean(err**2,axis=0)).tolist(),'median_abs_error':np.median(abs(err),axis=0).tolist(),'q90_abs_error':np.quantile(abs(err),.9,axis=0).tolist(),'fraction_all_errors_below_0_1':float(np.mean(np.max(abs(err),axis=1)<.1)),'boundary_fits':edge,'optimizer_failure_flags':fail,'max_projected_gradient_sup':max(v['projected_gradient_sup'] for v in records if v['N']==N),'local_fisher_sd':np.sqrt(np.diag(Finv)/N).tolist()})
# Exact-law optimization controls at three admitted sources.
controls=[]
for z in [truth,np.array([.8,2.5,.7]),np.array([1.3,2.8,1.3])]:
 p,_=law(z);r=fit(p);controls.append({'truth':z.tolist(),'estimate':r.x.tolist(),'max_error':float(max(abs(r.x-z))),'optimizer_success':bool(r.success)})
out={'status':'executed synthetic floating-point likelihood benchmark; not validated global optimization or coverage theorem','seed':20261025,'truth':truth.tolist(),'bounds':bounds,'sufficient_statistic':'K = number of base matches in a three-site pair locus; K=0,1,2,3','truth_status_probabilities':p0.tolist(),'fisher_information_per_locus':F.tolist(),'fisher_eigenvalues':ev.tolist(),'weakest_direction':U[:,0].tolist(),'inverse_fisher_diagonal':np.diag(Finv).tolist(),'rival_unrounded':z1.tolist(),'rival_rational_candidate':z1_rounded,'rival_chi_square_float':float(chi),'rival_pinsker_required_N_float':float(1.62/chi),'results':rows,'exact_law_fit_controls':controls,'records':records}
Path(__file__).with_name('unknown-calendar-likelihood-benchmark.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
