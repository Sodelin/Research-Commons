#!/usr/bin/env python3
"""Exact pair-law/recurrence controls on rational-exponential parameter cases.
Time is rescaled x=(8/3)t. Rates a=r/(8/3) are positive integers and
boundaries are integer multiples of log(2), making every checked moment rational.
This is supplementary evidence, not an exhaustive parameter or all-L proof.
"""
from fractions import Fraction as F
from pathlib import Path
import json

def pow2(q): return F(2)**(-q)
def coeff_mul(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return out

def pieces(par,pair):
    A,B,C,AB,R=par['rates'];h,u,v=par['durations'];g=par['g']
    t1=h+u;t0=t1+v;s=pow2(B*h)
    if pair=='AC': return [(t0,None,R,R)]
    if pair=='AB': return [(t1,t0,AB,(1-g)*AB),(t0,None,R,(g+(1-g)*pow2(AB*v))*R)]
    if pair=='BC': return [(h,t0,C,g*C),(t0,None,R,(1-g+g*pow2(C*(u+v)))*R)]
    if pair=='AA': return [(0,t1,A,A),(t1,t0,AB,pow2(A*t1)*AB),(t0,None,R,pow2(A*t1+AB*v)*R)]
    if pair=='CC': return [(0,t0,C,C),(t0,None,R,pow2(C*t0)*R)]
    if pair=='BB': return [(0,h,B,B),(h,t1,B,s*(1-g)**2*B),(h,t1,C,s*g*g*C),
      (t1,t0,AB,s*(1-g)**2*pow2(B*u)*AB),(t1,t0,C,s*g*g*pow2(C*u)*C),
      (t0,None,R,s*((1-g)**2*pow2(B*u+AB*v)+g*g*pow2(C*(u+v))+2*g*(1-g))*R)]
    raise ValueError(pair)

def moment(par,pair,k):
    ans=F(0)
    for left,right,rate,amp in pieces(par,pair):
        ans+=amp/F(rate+k)*(pow2(k*left)-(pow2(rate*(right-left)+k*right) if right is not None else 0))
    return ans

def chain(rates,lengths,k):
    # Conditional starting-age-zero coalescence transform along finite phases
    # followed by a root population; a separate route-mixture construction.
    ans=F(rates[-1],rates[-1]+k)
    for rate,d in reversed(list(zip(rates[:-1],lengths))):
        surv=pow2((rate+k)*d)
        ans=F(rate,rate+k)*(1-surv)+surv*ans
    return ans

def direct(par,pair,k):
    A,B,C,AB,R=par['rates'];h,u,v=par['durations'];g=par['g'];t1=h+u;t0=t1+v
    root=F(R,R+k)
    if pair=='AA': return chain([A,AB,R],[t1,v],k)
    if pair=='CC': return chain([C,R],[t0],k)
    if pair=='AC': return pow2(k*t0)*root
    if pair=='AB': return (1-g)*pow2(k*t1)*chain([AB,R],[v],k)+g*pow2(k*t0)*root
    if pair=='BC': return g*pow2(k*h)*chain([C,R],[u+v],k)+(1-g)*pow2(k*t0)*root
    if pair=='BB':
        route=(1-g)**2*chain([B,AB,R],[u,v],k)+g*g*chain([C,R],[u+v],k)+2*g*(1-g)*pow2(k*(u+v))*root
        return F(B,B+k)*(1-pow2((B+k)*h))+pow2((B+k)*h)*route

pairs=['AA','BB','CC','AB','BC','AC']
params=[{'rates':(1,2,3,4,5),'durations':(1,2,3),'g':F(2,7)},
        {'rates':(2,2,2,2,2),'durations':(2,1,2),'g':F(3,5)},
        {'rates':(3,1,3,1,4),'durations':(1,1,1),'g':F(1,2)}]
rate_indices={'AA':(0,3,4),'BB':(1,2,3,4),'CC':(2,4),'AB':(3,4),'BC':(2,4),'AC':(4,)}
expected_order={'AA':30,'BB':56,'CC':12,'AB':16,'BC':16,'AC':4}
checks=0
for par in params:
    for pair in pairs:
        assert moment(par,pair,0)==1
        for k in range(21):
            assert moment(par,pair,k)==direct(par,pair,k)
            assert 0<moment(par,pair,k)<=1
            checks+=1

recurrence_checks=0; orders={}
p,q=params[:2]
for pair in pairs:
    inds=rate_indices[pair];degree=2*len(inds)-1
    boundaries=set()
    for par in [p,q]:
        for left,right,_,_ in pieces(par,pair):
            boundaries.add(left)
            if right is not None:boundaries.add(right)
    bases=[pow2(b) for b in sorted(boundaries)]
    annih=[F(1)]
    for base in bases:
        for _ in range(degree+1):annih=coeff_mul(annih,[-base,F(1)])
    order=len(annih)-1
    assert order<=expected_order[pair] and annih[-1]==1
    orders[pair]=order
    def H(k):
        den=F(1)
        for par in [p,q]:
            for i in inds:den*=par['rates'][i]+k
        return den*(moment(p,pair,k)-moment(q,pair,k))
    vals=[H(k) for k in range(order+4)]
    for k in range(4):
        assert sum(annih[i]*vals[k+i] for i in range(order+1))==0
        recurrence_checks+=1
result={'status':'PASS','arithmetic':'Integer and Fraction only; exact rational exponential cases',
        'parameter_cases':3,'includes_all_equal_and_partly_equal_population_rates':True,
        'normalized_pair_laws':18,'route_mixture_vs_density_moment_checks':checks,
        'exact_recurrence_checks':recurrence_checks,'observed_orders':orders,
        'proved_order_bounds':expected_order,'site_bound':55,
        'limits':'Supplementary finite controls. Projectivity, global parameter recovery and all-parameter recurrence bounds are hand-proof obligations.'}
Path(__file__).with_name('PAIR-CONTROL-RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
