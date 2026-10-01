import numpy as np
from scipy.optimize import least_squares
from math import comb
rng=np.random.default_rng(20261002)
for M in [7,8,9]:
 ls=np.array([comb(j,2) for j in range(2,M+1)],float)
 y=ls*np.log(.5)+np.log(.5)+np.log(1-.4+.4*.3**ls)+np.log(1-.6+.6*.7**ls)
 for n in [3,4,5]:
  best=1e10;bp=None;found=False
  for rep in range(15):
   x=np.r_[rng.uniform(.4,.65),rng.uniform(.05,.85,n),rng.uniform(.05,.95,n)]
   def fun(x):
    return ls*np.log(x[0])+np.sum(np.log(1-x[1:1+n,None]+x[1:1+n,None]*x[1+n:,None]**ls),axis=0)-y
   r=least_squares(fun,x,bounds=(1e-9,1-1e-9),max_nfev=3000,ftol=1e-13,xtol=1e-13,gtol=1e-13)
   err=np.linalg.norm(r.fun,np.inf)
   if err<best:best=err;bp=r.x
   if err<1e-10 and np.min(np.r_[r.x,1-r.x])>1e-5:found=True;break
  print(M,n,'best',best,'params',bp,'strict numeric solution',found,flush=True)
