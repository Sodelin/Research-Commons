#!/usr/bin/env python3
"""Exact rational-exponential formula comparison; supplementary finite controls.
Uses the accepted density pieces, separately assembled from the new H/S/R form.
Time=(log 2)/(8/3) times an integer; physical rates=(8/3) times integers.
"""
from fractions import Fraction as F
import json

def e(n): return F(2)**(-n)
def density_moment(par,pair,k):
 A,B,C,AB,R=par['rates'];h,u,v=par['durations'];g=par['g'];t1=h+u;t0=t1+v;s=e(B*h)
 if pair=='AC':pieces=[(t0,None,R,R)]
 elif pair=='AB':pieces=[(t1,t0,AB,(1-g)*AB),(t0,None,R,(g+(1-g)*e(AB*v))*R)]
 elif pair=='BC':pieces=[(h,t0,C,g*C),(t0,None,R,(1-g+g*e(C*(u+v)))*R)]
 elif pair=='AA':pieces=[(0,t1,A,A),(t1,t0,AB,e(A*t1)*AB),(t0,None,R,e(A*t1+AB*v)*R)]
 elif pair=='CC':pieces=[(0,t0,C,C),(t0,None,R,e(C*t0)*R)]
 elif pair=='BB':pieces=[(0,h,B,B),(h,t1,B,s*(1-g)**2*B),(h,t1,C,s*g*g*C),(t1,t0,AB,s*(1-g)**2*e(B*u)*AB),(t1,t0,C,s*g*g*e(C*u)*C),(t0,None,R,s*((1-g)**2*e(B*u+AB*v)+g*g*e(C*(u+v))+2*g*(1-g))*R)]
 else:raise ValueError(pair)
 return sum(amp/F(r+k)*(e(k*l)-(e(r*(rr-l)+k*rr) if rr is not None else 0)) for l,rr,r,amp in pieces)

def formulas(par,k):
 A,B,C,AB,R=par['rates'];h,u,v=par['durations'];g=par['g'];t1=h+u;t0=t1+v
 H=lambda r,l:F(r,r+k)*(1-e((r+k)*l)); root=F(R,R+k)
 sb=e(B*h); b=e(B*u); a=e(AB*v); c1=e(C*(u+v));a0=e(A*t1);c0=e(C*t0)
 return {'AC':e(k*t0)*root,
 'AB':(1-g)*e(k*t1)*H(AB,v)+(g+(1-g)*a)*e(k*t0)*root,
 'BC':g*e(k*h)*H(C,u+v)+(1-g+g*c1)*e(k*t0)*root,
 'AA':H(A,t1)+a0*e(k*t1)*H(AB,v)+a0*a*e(k*t0)*root,
 'CC':H(C,t0)+c0*e(k*t0)*root,
 'BB':H(B,h)+sb*((1-g)**2*e(k*h)*H(B,u)+g*g*e(k*h)*H(C,u+v)+(1-g)**2*b*e(k*t1)*H(AB,v)+((1-g)**2*b*a+g*g*c1+2*g*(1-g))*e(k*t0)*root)}
params=[{'rates':(1,2,3,4,5),'durations':(1,2,3),'g':F(2,7)}, {'rates':(2,2,2,2,2),'durations':(2,1,2),'g':F(3,5)}, {'rates':(3,1,3,1,4),'durations':(1,1,1),'g':F(1,2)}]
checks=0
for par in params:
 for k in range(56):
  for pair,m in formulas(par,k).items():
   assert m==density_moment(par,pair,k)
   assert 0<m<=1
   if k==0:assert m==1
   checks+=1
print(json.dumps({'status':'PASS','exact_formula_vs_density_checks':checks,'parameter_cases':3,'k_range':[0,55],'includes_equal_and_partly_equal_rates':True,'limitations':'Finite rational-exponential checks, not general injectivity or an inverse-domain execution.'},indent=2))
