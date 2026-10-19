from fractions import Fraction as F
from math import isqrt
import json
import sympy as s
z=s.symbols('z')
q=z**10-F(11323,59136)*z**6+F(8571,315392)*z**3-F(723,180224)*z+F(1181,1892352)
fac=(2*z-1)**2*(4*z-1)**2*(59136*z**6+88704*z**5+85008*z**4+66528*z**3+35108*z**2+13161*z+2362)/3784704
assert s.expand(q-fac)==0
# W=E(1/2) B_COMMON(1/8,1/4,1/2) E(1/2)
# W has arm products 1/32 and 1/16. Q(z)=q(2z).
Q=s.Poly(s.expand(q.subs(z,2*z)),z)
assert set(m[0] for m,c in Q.terms())=={0,1,3,6,10}
lo=hi=F(0);rows=[];bits=100;scale=1<<bits
for (k,),c in Q.terms():
    c=F(int(s.numer(c)),int(s.denom(c)))
    m=(F(1,32)**k+F(1,16)**k)/2
    v=isqrt((m.numerator*scale*scale)//m.denominator)
    l=F(v,scale);u=F(v+1,scale)
    assert l*l<=m<=u*u
    lo+=c*(l if c>=0 else u)
    hi+=c*(u if c>=0 else l)
    rows.append({'rate':k,'coefficient':str(c),'original_moment':str(m),'root_lower':str(l),'root_upper':str(u)})
assert hi<F(-6,10**6)
assert lo<F(0)
out={'status':'PASS','root_bits':bits,'lower':str(lo),'upper':str(hi),'upper_decimal_display':float(hi),'rows':rows,'scope':'Exact scalar finite-signature rejection only; no full G3 decision theorem.'}
open('RESULT.json','w').write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
