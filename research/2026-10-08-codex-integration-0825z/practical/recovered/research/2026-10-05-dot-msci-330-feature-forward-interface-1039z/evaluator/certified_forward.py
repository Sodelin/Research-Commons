"""Bounded rational-interval forward evaluator for the fixed six-copy pulse family.
No data likelihood fit, posterior inference, optimizer, or inverse search.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import re

PAIRS=('AA','BB','CC','AB','BC','AC')
PARAMETERS=('h','t1','t0','g','rA','rB','rC','rAB','rR')
MAX_INPUT_BITS=256

class DomainError(ValueError):pass
class ResourceBound(ValueError):pass

def rational(x):
    if isinstance(x,bool) or isinstance(x,float):raise DomainError('exact rational input required')
    if isinstance(x,str) and len(x)>160:raise ResourceBound('raw rational text exceeds160 characters')
    if isinstance(x,F):v=x
    elif isinstance(x,int):v=F(x)
    elif isinstance(x,str) and re.fullmatch(r'-?\d+(?:/[1-9]\d*)?',x):v=F(x)
    else:raise DomainError('integer or rational n/d string required')
    if max(abs(v.numerator).bit_length(),v.denominator.bit_length())>MAX_INPUT_BITS:raise ResourceBound('reduced rational exceeds256 bits')
    return v

def validate(p):
    if set(p)!=set(PARAMETERS):raise DomainError('exact nine-parameter key set required')
    p={k:rational(p[k]) for k in PARAMETERS}
    if not (0<p['h']<p['t1']<p['t0'] and 0<p['g']<1):raise DomainError('strict pulse/time domain required')
    if any(p[k]<=0 for k in PARAMETERS if k.startswith('r')):raise DomainError('positive pair rates required')
    return p

@dataclass(frozen=True)
class Interval:
    lo:F
    hi:F
    def __post_init__(self):
        object.__setattr__(self,'lo',F(self.lo));object.__setattr__(self,'hi',F(self.hi))
        if self.lo>self.hi:raise ValueError('reversed interval')
    @staticmethod
    def point(v):return Interval(F(v),F(v))
    @staticmethod
    def cast(v):return v if isinstance(v,Interval) else Interval.point(v)
    def __add__(self,other):
        o=self.cast(other);return Interval(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,other):return self+-self.cast(other)
    def __rsub__(self,other):return self.cast(other)+-self
    def __mul__(self,other):
        o=self.cast(other);v=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi];return Interval(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,other):
        v=F(other)
        if v==0:raise ZeroDivisionError
        return self*F(1,v)
    @property
    def width(self):return self.hi-self.lo
    def contains(self,x):return self.lo<=F(x)<=self.hi
    def intersects(self,other):return max(self.lo,other.lo)<=min(self.hi,other.hi)
    def dyadic(self,bits):
        scale=1<<bits
        lo=(self.lo*scale).__floor__();hi=(self.hi*scale).__ceil__()
        return Interval(F(lo,scale),F(hi,scale))
    def unit_intersection(self):
        return Interval(max(F(0),self.lo),min(F(1),self.hi))
    def record(self):return {'lower':str(self.lo),'upper':str(self.hi),'width':str(self.width)}

@lru_cache(maxsize=8192,typed=True)
def exp_neg(x,bits):
    """Certified e^(-x), rational x>=0, width<=2^-bits; no floating point."""
    if isinstance(x,(float,bool)) or not isinstance(x,(int,F)):raise DomainError('exact rational exponential input required')
    x=F(x)
    if x<0 or not isinstance(bits,int) or isinstance(bits,bool) or not 8<=bits<=192:raise DomainError('exponential domain/precision')
    if x==0:return Interval.point(1)
    if x>=bits:return Interval(F(0),F(1,1<<bits)) # e>2
    u=x;m=0
    while u>1:u/=2;m+=1
    q=bits+m+4;tol=F(1,1<<q);lower=F(0);upper=F(1);s=F(1);term=F(1)
    for j in range(1,513):
        term*=u/F(j);s+=-term if j%2 else term
        if j%2:lower=s
        else:upper=s
        if upper-lower<=tol:break
    else:raise ResourceBound('Taylor term cap exceeded')
    ans=Interval(lower,upper).dyadic(q).unit_intersection()
    for _ in range(m):ans=Interval(ans.lo*ans.lo,ans.hi*ans.hi).dyadic(q).unit_intersection()
    if ans.width>F(1,1<<bits):raise ArithmeticError('exponential width contract failed')
    return ans

def pair_expressions(p,z,E):
    """Shared exact source parameters; E(a) encloses/represents exp(-a)."""
    if isinstance(z,(float,bool)) or not isinstance(z,(int,F)):raise DomainError('exact rational Laplace argument required')
    z=F(z)
    if z<0:raise DomainError('nonnegative Laplace argument required')
    h,t1,t0,g=(p[k] for k in ('h','t1','t0','g'))
    a,b,c,d,r=(p[k] for k in ('rA','rB','rC','rAB','rR'))
    u=t1-h;v=t0-t1;w=t0-h
    S=lambda rate,length:E(rate*length)
    H=lambda rate,length:rate/(rate+z)*(1-E((rate+z)*length))
    tail=E(z*t0)*(r/(r+z));s=S(b,h);sb=S(b,u);sd=S(d,v);sc=S(c,w);sa=S(a,t1)
    return {
      'AC':tail,
      'AB':(1-g)*E(z*t1)*H(d,v)+(g+(1-g)*sd)*tail,
      'BC':g*E(z*h)*H(c,w)+(1-g+g*sc)*tail,
      'AA':H(a,t1)+sa*E(z*t1)*H(d,v)+sa*sd*tail,
      'CC':H(c,t0)+S(c,t0)*tail,
      'BB':H(b,h)+s*((1-g)**2*(E(z*h)*H(b,u)+sb*E(z*t1)*H(d,v))+g*g*E(z*h)*H(c,w)+((1-g)**2*sb*sd+g*g*sc+2*g*(1-g))*tail)
    }

def evaluate(p,bits=64):
    p=validate(p)
    if not isinstance(bits,int) or isinstance(bits,bool) or not 16<=bits<=128:raise DomainError('output bits must be16..128')
    for guard in (12,20,28):
        means={pair:[] for pair in PAIRS};moments={pair:[] for pair in PAIRS}
        for k in range(1,56):
            m=pair_expressions(p,F(8*k,3),lambda x:exp_neg(x,bits+guard))
            for pair in PAIRS:
                moment=m[pair].unit_intersection().dyadic(bits+3).unit_intersection()
                mean=((1+m[pair])/2).unit_intersection().dyadic(bits+3).unit_intersection()
                moments[pair].append(moment);means[pair].append(mean)
        if all(v.width<=F(1,1<<bits) for table in (means,moments) for row in table.values() for v in row):return p,moments,means
    raise ResourceBound('output-width contract not reached at bounded precision')

def report(p,bits=64):
    p,moments,means=evaluate(p,bits)
    return {'schema':'fixed-pulse-certified-forward-v1','parameters':{k:str(v) for k,v in p.items()},'parameterization':'rP=2/thetaP; B and C rates tied across pulse sides','channel':'six labelled phased copies, two/population; known homogeneous stationary clock-JC;55 sites share one genealogy','feature_count':330,'output_width_bound':str(F(1,1<<bits)),'features':{pair:[{'k':k+1,'laplace_argument':str(F(8*(k+1),3)),'laplace_interval':moments[pair][k].record(),'mean_interval':means[pair][k].record()} for k in range(55)] for pair in PAIRS},'floating_point_used_for_certification':False,'estimator_or_inverse_search':False,'data_fit':False,'probabilistic_confidence_claimed':False}
