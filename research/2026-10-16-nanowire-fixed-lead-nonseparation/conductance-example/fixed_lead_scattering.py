"""Own exact-outward-rounded zero-energy scattering bound for the declared 60-site model.
Every matrix inverse/division must certify nonzero pivots; failure is not acceptance.
"""
from dyadic_interval import *
N=60;lam=F('2.5');B=F(2);Delta=F('.2')
def scattering(a,M,t):
 T=[[-t,0,-lam,0],[0,t,0,lam],[lam,0,-t,0],[0,-lam,0,t]]
 U=[[-x for x in row] for row in T];L=[list(x) for x in zip(*U)]
 def onsite(a,contact):
  H=[[a,Delta,B,0],[Delta,-a,0,B],[B,0,a,Delta],[0,B,Delta,-a]]
  return [[C(-H[i][j],int(contact and i==j)) for j in range(4)] for i in range(4)]
 K=onsite(I(M),True)
 for j in range(N-2,-1,-1):
  K=sub(onsite(I(M) if j==0 else a,j==0),mm(mm(U,inverse(K)),L))
 G=inverse(K)
 r=[[C(int(i==j))-C(0,2)*G[i][j] for j in range(4)] for i in range(4)]
 tv=determinant(r)
 return {'real':tv.r.out(),'imag':tv.i.out(),'r':[[{'real':x.r.out(),'imag':x.i.out()} for x in row] for row in r]}
