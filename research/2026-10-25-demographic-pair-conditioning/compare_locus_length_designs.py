"""Source-local positive-quadrature Fisher comparison at fixed nucleotide cost."""
import json
from pathlib import Path
import numpy as np
from scipy.special import roots_legendre,roots_laguerre,gammaln
from scipy.optimize import minimize
class PairLaw:
 def __init__(self,L,order=96):
  self.L=L;self.k=np.arange(L+1)[:,None]
  self.logbin=(gammaln(L+1)-gammaln(self.k+1)-gammaln(L-self.k+1))
  self.a,self.wa=roots_legendre(order);self.v,self.wv=roots_laguerre(order)
 def g(self,T):
  q=(1+3*np.exp(-T))/4
  return np.exp(self.logbin+self.k*np.log(q)+(self.L-self.k)*np.log1p(-q))
 def __call__(self,z):
  x,y,t=z;T=(self.a+1)*t/2;g=self.g(T)
  w=self.wa*t/2*x*np.exp(-x*T)
  first=g@w;dx=g@(w*(1/x-T))
  v=self.v;g=self.g(t+v/y);w=self.wv*np.exp(-x*t)
  tail=g@w;dy=g@(w*(1-v)/y)
  p=first+tail
  dt=(y-x)*(tail-np.exp(-x*t)*self.g(np.array([t]))[:,0])
  return p,np.array([dx-t*tail,dy,dt]).T

def evaluate():
 truth=np.array([1.,2.,1.]);bounds=[(.5,1.5),(1.75,3.),(.5,1.5)];rows=[]
 for L in [3,4,6,8,12,16,24,32,48,64,96,128,192,256]:
  law=PairLaw(L);p,J=law(truth);ph,Jh=PairLaw(L,192)(truth)
  F=J.T@np.diag(1/p)@J;Finv=np.linalg.inv(F);ev=np.linalg.eigvalsh(F/(2*L))
  def rivalfun(v):
   q,G=law([v[0],2.2,v[1]])
   return np.sum(p*np.log(p/q)),(-G.T@(p/q))[[0,2]]
  rr=minimize(rivalfun,[1.,1.],jac=True,bounds=[bounds[0],bounds[2]],method='L-BFGS-B',options={'ftol':1e-16,'gtol':1e-12,'maxiter':1000})
  z1=[rr.x[0],2.2,rr.x[1]];q,_=law(z1)
  rows.append({'L':L,'status_probability_sum':float(sum(p)),'derivative_sum_sup':float(max(abs(J.sum(axis=0)))),'quadrature_96_192_probability_difference':float(max(abs(p-ph))),'quadrature_96_192_jacobian_difference':float(np.max(abs(J-Jh))),'fisher_eigenvalues_per_call':ev.tolist(),'asymptotic_variance_times_nucleotide_budget':(2*L*np.diag(Finv)).tolist(),'F_yy':float(F[1,1]),'genealogy_F_yy_upper':float(np.exp(-1)/4),'rival_rational':[f'{z1[0]:.10f}','2.2',f'{z1[2]:.10f}'],'rival_chi2':float(sum((q-p)**2/p)),'rival_fit_success':bool(rr.success)})
 out={'status':'floating positive-quadrature source-local design diagnostic, not a finite-data guarantee','truth':truth.tolist(),'clock_s':1,'site_lengths_are_changed_experiments':True,'budget_unit':'one nucleotide call; each independent locus costs 2L','rows':rows}
 Path(__file__).with_name('locus-length-fisher-design.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':evaluate()
