"""Certified natural inclusions; reuses the pinned published exponential primitive."""
import hashlib,importlib.util,sys
from fractions import Fraction as F
from pathlib import Path
BASE=Path(__file__).resolve().parent
SOURCE=BASE.parent/'msci-330-feature-public-20261005-1039z/evaluator/certified_forward.py'
SOURCE_SHA='c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace'
if hashlib.sha256(SOURCE.read_bytes()).hexdigest()!=SOURCE_SHA:raise RuntimeError('certified exponential source identity mismatch')
_spec=importlib.util.spec_from_file_location('_sequential_pinned_forward',SOURCE);forward=importlib.util.module_from_spec(_spec);sys.modules[_spec.name]=forward;_spec.loader.exec_module(forward)
I=forward.Interval
BITS=80
MAX_INTERMEDIATE_BITS=2048
class Unsupported(ValueError):pass
class Inconsistent(ValueError):pass

def size_guard(v):
    v=F(v)
    if max(abs(v.numerator).bit_length(),v.denominator.bit_length())>MAX_INTERMEDIATE_BITS:raise Unsupported('intermediate rational cap')
    return v

def rounded(x):
    size_guard(x.lo);size_guard(x.hi);return x.dyadic(BITS)
def meet(a,b):
    low=max(a.lo,b.lo);high=min(a.hi,b.hi)
    if low>high:raise Inconsistent('empty closed interval intersection')
    return I(low,high)
def add(a,b):return rounded(a+b)
def sub(a,b):return rounded(a-b)
def mul(a,b):return rounded(a*b)
def reciprocal(a):
    if a.lo<=0<=a.hi:raise Unsupported('denominator interval contains zero')
    return rounded(I(1/a.hi,1/a.lo))
def divide(a,b):return mul(a,reciprocal(b))
def exact_square(a):
    if a.lo<=0<=a.hi:return I(F(0),max(a.lo*a.lo,a.hi*a.hi))
    return I(min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi))
def E(x):
    if x.lo<0:raise Unsupported('negative exponential argument')
    size_guard(x.lo);size_guard(x.hi)
    return I(forward.exp_neg(x.hi,BITS).lo,forward.exp_neg(x.lo,BITS).hi)
def S(rate,length):
    if rate.lo<=0 or length.lo<0:raise Unsupported('invalid S domain')
    return E(I(size_guard(rate.lo*length.lo),size_guard(rate.hi*length.hi)))
def R(z,rate):
    if z<=0 or rate.lo<=0:raise Unsupported('invalid R domain')
    return rounded(I(rate.lo/(rate.lo+z),rate.hi/(rate.hi+z)))
def H(z,rate,length):
    if z<=0 or rate.lo<=0 or length.lo<0:raise Unsupported('invalid H domain')
    def endpoint(r,l):
        e=forward.exp_neg(size_guard((r+z)*l),BITS)
        return (1-e)*(r/(r+z))
    return rounded(I(endpoint(rate.lo,length.lo).lo,endpoint(rate.hi,length.hi).hi))
def ez(z,length):return E(I(size_guard(z*length.lo),size_guard(z*length.hi)))
def tail(z,T,root):return mul(ez(z,T),R(z,root))
def two_stage(z,onset,rate,length,T,root):return add(mul(ez(z,onset),H(z,rate,length)),mul(S(rate,length),tail(z,T,root)))

def pair_intervals(physical,aux,z):
    h,u,v,g=(physical[k] for k in ('h','u','v','g'));a,b,c,d,r=(physical[k] for k in ('rA','rB','rC','rAB','rR'));A,T,L=(aux[k] for k in ('A','T','L'))
    one=I.point(1);q=sub(one,g);q2=mul(q,q);g2=mul(g,g);root=tail(z,T,r)
    sbh=S(b,h);sbu=S(b,u);sdv=S(d,v);scL=S(c,L);saA=S(a,A)
    AB=add(mul(mul(q,ez(z,A)),H(z,d,v)),mul(add(g,mul(q,sdv)),root))
    BC=add(mul(mul(g,ez(z,h)),H(z,c,L)),mul(add(q,mul(g,scL)),root))
    AA=add(add(H(z,a,A),mul(mul(saA,ez(z,A)),H(z,d,v))),mul(mul(saA,sdv),root))
    CC=add(H(z,c,T),mul(S(c,T),root))
    stays=add(mul(ez(z,h),H(z,b,u)),mul(mul(sbu,ez(z,A)),H(z,d,v)))
    routes=mul(ez(z,h),H(z,c,L))
    rootweight=add(add(mul(mul(q2,sbu),sdv),mul(g2,scL)),mul(I.point(2),mul(g,q)))
    BB=add(H(z,b,h),mul(sbh,add(add(mul(q2,stays),mul(g2,routes)),mul(rootweight,root))))
    return {name:meet(value,I(0,1)) for name,value in dict(AC=root,AB=AB,BC=BC,AA=AA,CC=CC,BB=BB).items()}
FEATURES=('AC1','AC2','CC1','BC1','BC2','AB1','AB2','AA1','BB1')
def selected(physical,aux):
    byk={k:pair_intervals(physical,aux,F(8*k,3)) for k in (1,2)}
    return {name:byk[int(name[-1])][name[:-1]] for name in FEATURES}
