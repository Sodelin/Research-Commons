"""Conditional pair geometry only; no source evaluation/data/cover admission."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import importlib.util
import sys

FEATURES = ('AC1','AC2','CC1','BC1','BC2','AB1','AB2','AA1','BB1')
PHYSICAL = ('h','u','v','rA','rB','rC','rAB','rR','g')
DOMAIN = {k:('1/32','1/8') if k in ('h','u','v') else
          ('1/6','2/3') if k=='g' else ('1/2','6') for k in PHYSICAL}
PROVIDER = 'research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py'
PROVIDER_SHA = 'c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace'


class Refusal(Exception):
    pass


class Arithmetic:
    def __init__(self, root, precision, max_bits, max_exp_calls):
        if type(precision) is not int or not 64<=precision<=128:
            raise Refusal('PRECISION')
        if type(max_bits) is not int or not 256<=max_bits<=16384:
            raise Refusal('BIT_BUDGET')
        if type(max_exp_calls) is not int or not 0<=max_exp_calls<=32:
            raise Refusal('EXP_BUDGET')
        self.precision,self.max_bits,self.max_exp_calls=precision,max_bits,max_exp_calls
        self.exp_calls=0
        self.path=Path(root)/PROVIDER
        self.authenticate()
        spec=importlib.util.spec_from_file_location('_signed_receiver_exp',self.path)
        module=importlib.util.module_from_spec(spec)
        sys.modules[spec.name]=module
        spec.loader.exec_module(module)
        self.scalar_exp=module.exp_neg

    def authenticate(self):
        if self.path.is_symlink() or hashlib.sha256(self.path.read_bytes()).hexdigest()!=PROVIDER_SHA:
            raise Refusal('SOURCE_IDENTITY')

    def check(self,q):
        if max(q.numerator.bit_length(),q.denominator.bit_length())>self.max_bits:
            raise Refusal('ARITHMETIC_BITS')

    def interval(self,lo,hi=None):
        return Interval(self,F(lo),F(lo if hi is None else hi))

    def exp_neg(self,x):
        x=self.coerce(x)
        if x.lo<0:raise Refusal('EXP_DOMAIN')
        if self.exp_calls+2>self.max_exp_calls:raise Refusal('EXP_CALLS')
        self.exp_calls+=2
        lo=self.scalar_exp(x.hi,self.precision+4).lo
        hi=self.scalar_exp(x.lo,self.precision+4).hi
        return self.interval(lo,hi)

    def coerce(self,x):
        if isinstance(x,Interval):
            if x.math is not self:raise Refusal('ARITHMETIC_CONTEXT')
            return x
        return self.interval(x)


class Interval:
    def __init__(self,math,lo,hi):
        if lo>hi:raise Refusal('EMPTY_INTERVAL')
        math.check(lo);math.check(hi)
        scale=1<<math.precision
        self.math=math
        self.lo=F((lo*scale).numerator//(lo*scale).denominator,scale)
        q=hi*scale
        self.hi=F(-((-q.numerator)//q.denominator),scale)

    def __add__(self,x):
        x=self.math.coerce(x);return self.math.interval(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __neg__(self):return self.math.interval(-self.hi,-self.lo)
    def __sub__(self,x):return self+-self.math.coerce(x)
    def __rsub__(self,x):return self.math.coerce(x)+-self
    def __mul__(self,x):
        x=self.math.coerce(x)
        v=[a*b for a in (self.lo,self.hi) for b in (x.lo,x.hi)]
        return self.math.interval(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=self.math.coerce(x)
        if x.lo<=0<=x.hi:raise Refusal('DENOMINATOR')
        return self*self.math.interval(1/x.hi,1/x.lo)
    def __rtruediv__(self,x):return self.math.coerce(x)/self
    def abs_bound(self):return max(abs(self.lo),abs(self.hi))
    def meet(self,x):
        x=self.math.coerce(x)
        return self.math.interval(max(self.lo,x.lo),min(self.hi,x.hi))
    def record(self):return [str(self.lo),str(self.hi)]


def rational(x):
    if not isinstance(x,str):raise Refusal('RATIONAL_INPUT')
    q=F(x)
    if max(q.numerator.bit_length(),q.denominator.bit_length())>256:
        raise Refusal('INPUT_BITS')
    return q


def box(math,record,keys,domain):
    if not isinstance(record,dict) or set(record)!=set(keys):raise Refusal('KEYS')
    result={}
    for k in keys:
        pair=record[k]
        if not isinstance(pair,(list,tuple)) or len(pair)!=2:raise Refusal('ENDPOINTS')
        lo,hi=map(rational,pair)
        left,right=map(F,domain[k])
        if not left<=lo<=hi<=right:raise Refusal('INPUT_DOMAIN')
        result[k]=math.interval(lo,hi)
    return result


def receive(root,means0,means1,physical0=None,physical1=None,
            precision=96,max_bits=4096,max_exp_calls=24):
    result={'schema':'original-signed-nine-pair-receiver-v1','status':'UNKNOWN',
            'data_confidence_certificate_issued':False,'outer_cover_validated':False,
            'actual_source_forward_evaluations':0,'observation_rows_replayed':0,
            'model':'original-fixed-six-copy-clock-jc-nine','target':'1/20',
            'original_domain':DOMAIN,'provider_sha256':PROVIDER_SHA}
    math=None
    try:
        math=Arithmetic(root,precision,max_bits,max_exp_calls)
        md={k:('0','1') for k in FEATURES}
        m0,m1=(box(math,x,FEATURES,md) for x in (means0,means1))
        p0,p1=(box(math,x if x is not None else DOMAIN,PHYSICAL,DOMAIN)
               for x in (physical0,physical1))
        for m in (m0,m1):
            for k in FEATURES:m[k]=m[k].meet(math.interval(F(1,2),1))
        dm={k:m0[k]-m1[k] for k in FEATURES}
        prior={k:p0[k]-p1[k] for k in PHYSICAL}
        A0,A1=(p['h']+p['u'] for p in (p0,p1))
        T0,T1=(p['h']+p['u']+p['v'] for p in (p0,p1))
        c=F(8,3)
        a0,a1=(2*m['AC1']-1 for m in (m0,m1))
        b1=2*m1['AC2']-1
        if a0.lo<=0 or a1.lo<=0:raise Refusal('ROOT_DENOMINATOR')
        rho1=b1/(a1*a1)
        ER=2*dm['AC2']-rho1*(a0+a1)*(2*dm['AC1'])
        R0,R1=p0['rR'],p1['rR']
        K=(R0*(R0+2*c)*R1*(R1+2*c)/
           (c*c*(R0+R1+2*c)*a0*a0)).meet(math.interval(0,851))
        DR=(-K*ER).meet(prior['rR'])
        JT=(1+c/R0)*(2*dm['AC1'])-a1*c*DR/(R0*R1)
        DT=(-math.interval(F(3,8),F(9,8))*JT).meet(T0-T1)
        CCexp=math.exp_neg(p1['rC']*T0)
        DC=((dm['CC1']-CCexp*dm['AC1']-
             math.interval(-F(48,29),F(48,29))*DT)/
            math.interval(F(3,377),F(3,16))).meet(prior['rC'])
        y0=m0['BC1']-m0['AC1'];y1=m1['BC1']-m1['AC1']
        if y0.lo<=0 or y1.lo<=0:raise Refusal('PULSE_DENOMINATOR')
        Q1=(m1['BC2']-m1['AC2'])/y1
        EH=(dm['BC2']-dm['AC2'])-Q1*(dm['BC1']-dm['AC1'])
        DH=((math.interval(-F(16,3),F(16,3))*DT+
             math.interval(0,F(1,8))*DC+
             math.interval(-F(12,19),F(12,19))*DR-EH/y0)/
            math.interval(F(4,9),F(208,51))).meet(prior['h'])
        g0,g1=p0['g'],p1['g']
        EG=dm['BC1']-(1-g1)*dm['AC1']-g1*dm['CC1']/math.exp_neg(p0['rC']*p0['h'])
        GN=math.interval(-24,24)*DH+math.interval(-F(3,4),F(3,4))*DC
        denominator=(y0/g0).meet(math.interval(F(1,275),1))
        DG=((EG-g1*GN/2)/denominator).meet(prior['g'])
        E=[];lift=[]
        for k,tc,rc in ((1,F(44,19),F(48,361)),(2,F(88,35),F(96,1225))):
            e=dm['AB'+str(k)]-g0*dm['AC'+str(k)]+DG*(m1['AB'+str(k)]-m1['AC'+str(k)])/(1-g1)
            E.append(e)
            lift.append(e/(1-g0)+math.interval(-tc,tc)*DT-math.interval(0,rc)*DR)
        BA=F(5*(1<<14)*(3**6))*(lift[1].abs_bound()+2*lift[0].abs_bound())
        DA=math.interval(-BA,BA).meet(A0-A1)
        Bd=4608*(lift[0].abs_bound()+3*DA.abs_bound())
        DD=math.interval(-Bd,Bd).meet(prior['rAB'])
        Ba=135*(dm['AA1'].abs_bound()+3*E[0].abs_bound()+F(7,4)*DA.abs_bound())
        DRA=math.interval(-Ba,Ba).meet(prior['rA'])
        b=p1['rB'];ea=math.exp_neg(b*A0);eh=math.exp_neg(b*p0['h'])
        EB=dm['BB1']-(1-g0)*ea*dm['AB1']-g0*eh*dm['BC1']-g0*(1-g0)*(eh-ea)*dm['AC1']
        Bb=240*(EB.abs_bound()+F(20,11)*DA.abs_bound()+F(128,57)*DH.abs_bound()+F(11,8)*DG.abs_bound())
        DB=math.interval(-Bb,Bb).meet(prior['rB'])
        difference={'h':DH,'u':(DA-DH).meet(prior['u']),
                    'v':(DT-DA).meet(prior['v']),'rA':DRA,'rB':DB,
                    'rC':DC,'rAB':DD,'rR':DR,'g':DG}
        normalized={k:v.abs_bound()/(F(DOMAIN[k][1])-F(DOMAIN[k][0]))
                    for k,v in difference.items()}
        maximum=max(normalized.values())
        math.authenticate()
        result.update(status='CONDITIONAL_PAIR_WIDTH_CERTIFIED' if maximum<F(1,20) else 'UNKNOWN',
                      difference_intervals={k:v.record() for k,v in difference.items()},
                      normalized_absolute_difference_bounds={k:str(v) for k,v in normalized.items()},
                      maximum_normalized_difference_bound=str(maximum),
                      signed_residuals={'root':ER.record(),'root_time':JT.record(),
                                        'h':EH.record(),'g':EG.record(),
                                        'AB1':E[0].record(),'AB2':E[1].record(),'BB1':EB.record()},
                      mean_band_coverage_admitted=False,compatible_source_existence_verified=False)
    except (Refusal,ValueError,TypeError,OSError,ZeroDivisionError,ArithmeticError) as error:
        result['refusal']=str(error)
    finally:
        result.update(precision_fractional_bits=precision,arithmetic_max_bits=max_bits,
                      scalar_exp_calls=math.exp_calls if math else 0)
    return result
