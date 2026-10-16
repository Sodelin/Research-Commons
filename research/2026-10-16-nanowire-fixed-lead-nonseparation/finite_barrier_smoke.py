"""Exploratory finite-M smoke check. Not used in rational proof acceptance."""
import numpy as np
from scipy.optimize import brentq
import json
N=60;nc=N-2;t=25.082173212433077;l=2.5;B=2.;d=.2
I=np.eye(2);X=np.array([[0,1],[1,0]]);Y=np.array([[0,-1j],[1j,0]]);Z=np.diag([1,-1]);k=np.kron
hhop=-t*k(I,Z)-1j*l*k(Y,Z)
up=np.array([[-t,l],[l,t]]);dn=np.array([[-t,-l],[-l,t]])
i=8;j=107; rows=[q for q in range(2*nc) if q!=i];cols=[q for q in range(2*nc) if q!=j]
def Ac(a,M):
 A=np.zeros((2*nc,2*nc));o=np.array([[a,-B+d],[B+d,-a]])
 for q in range(nc):
  A[2*q:2*q+2,2*q:2*q+2]=o
  if q<nc-1:A[2*q:2*q+2,2*q+2:2*q+4]=up;A[2*q+2:2*q+4,2*q:2*q+2]=dn
 ob=np.array([[M,-B+d],[B+d,-M]])
 A[:2,:2]-=dn@np.linalg.solve(ob,up);A[-2:,-2:]-=up@np.linalg.solve(ob,dn)
 return A
def f(a,M):
 A=Ac(a,M);return A[i,j]-A[i,cols]@np.linalg.solve(A[np.ix_(rows,cols)],A[rows,j])
def H(a,M,field=B):
 h=np.zeros((4*N,4*N),complex)
 for q in range(N):
  z=M if q in [0,N-1] else a
  h[4*q:4*q+4,4*q:4*q+4]=z*k(I,Z)+field*k(X,I)+d*k(I,X)
  if q<N-1:h[4*q:4*q+4,4*q+4:4*q+8]=hhop;h[4*q+4:4*q+8,4*q:4*q+4]=hhop.conj().T
 return h
out=[]
for M in [1000.,3000.,10000.]:
 a=brentq(lambda x:f(x,M),49.3,49.5,xtol=1e-14)
 item={'M':M,'a_closed_zero':a,'cases':[]}
 for c in [.01,100.]:
  h=H(a+c/M**2,M); inv=-h.copy();inv[:4,:4]+=1j*np.eye(4);inv[-4:,-4:]+=1j*np.eye(4)
  rhs=np.eye(4*N,4,dtype=complex);GLL=np.linalg.solve(inv,rhs)[:4,:]
  r=np.eye(4)-2j*GLL;tv=np.linalg.det(r)
  item['cases'].append({'c':c,'tv_real':float(tv.real),'tv_imag':float(tv.imag),'Es_at_test':float(min(abs(np.linalg.eigvalsh(h))))})
 out.append(item)
print(json.dumps(out,indent=2))
