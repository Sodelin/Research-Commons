"""Interval AD of the pinned smooth pair graph, with full physical-box derivatives."""
from dataclasses import dataclass
from fractions import Fraction as F
import interval_math as m
I=m.I
COORDS=('h','u','v','rA','rB','rC','rAB','rR','g')
ZERO=I.point(0);ONE=I.point(1)
@dataclass(frozen=True)
class AD:
    value:I
    gradient:tuple
    def __post_init__(self):
        if not isinstance(self.value,I) or len(self.gradient)!=9 or not all(isinstance(v,I) for v in self.gradient):raise ValueError('AD value/gradient schema')
    @staticmethod
    def cast(value):
        if isinstance(value,AD):return value
        if isinstance(value,(bool,float)) or not isinstance(value,(int,F,I)):raise ValueError('exact scalar/interval constant required')
        return AD(value if isinstance(value,I) else I.point(value),(ZERO,)*9)
    def __add__(self,other):
        other=self.cast(other);return AD(m.add(self.value,other.value),tuple(m.add(a,b) for a,b in zip(self.gradient,other.gradient)))
    __radd__=__add__
    def __neg__(self):return AD(-self.value,tuple(-x for x in self.gradient))
    def __sub__(self,other):return self+-self.cast(other)
    def __rsub__(self,other):return self.cast(other)+-self
    def __mul__(self,other):
        other=self.cast(other);return AD(m.mul(self.value,other.value),tuple(m.add(m.mul(a,other.value),m.mul(self.value,b)) for a,b in zip(self.gradient,other.gradient)))
    __rmul__=__mul__
    def reciprocal(self):
        inverse=m.reciprocal(self.value);factor=-m.mul(inverse,inverse)
        return AD(inverse,tuple(m.mul(factor,x) for x in self.gradient))
    def __truediv__(self,other):return self*self.cast(other).reciprocal()
    def __rtruediv__(self,other):return self.cast(other)*self.reciprocal()
    def __pow__(self,power):
        if type(power) is not int or power not in (0,1,2):raise ValueError('source graph only uses powers0,1,2')
        return self.cast(1) if power==0 else (self if power==1 else self*self)

def exp_negative(argument):
    argument=AD.cast(argument);value=m.E(argument.value)
    return AD(value,tuple(-m.mul(value,x) for x in argument.gradient))

def physical_pair_expressions(x,z,E):
    """Exact smooth substitution of the accepted graph, before interval evaluation.

    Direct u,v,L avoid the dependency-losing t1-h and t0-t1 reconstruction.
    No interval clipping or inherited auxiliary restriction is differentiated.
    """
    h,u,v,g=(x[key] for key in ('h','u','v','g'));t1=h+u;t0=t1+v;w=u+v
    a,b,c,d,r=(x[key] for key in ('rA','rB','rC','rAB','rR'))
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

def seed(value,index):return AD(value,tuple(ONE if j==index else ZERO for j in range(9)))
def evaluate(box):
    if set(box)!=set(COORDS) or any(not isinstance(box[key],I) for key in COORDS):raise ValueError('nine physical interval coordinates required')
    if any(box[key].lo<=0 for key in COORDS[:-1]) or not 0<box['g'].lo<=box['g'].hi<1:raise ValueError('strict physical source box required')
    x={key:seed(box[key],i) for i,key in enumerate(COORDS)}
    pairs={k:physical_pair_expressions(x,F(8*k,3),exp_negative) for k in (1,2)}
    selected=[pairs[int(key[-1])][key[:-1]] for key in m.FEATURES]
    return tuple(value.value for value in selected),tuple(value.gradient for value in selected)
