"""Exact rational example for the inherited cap-three I-word inequality.
No general observation-to-slot admission is supplied by this checker.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

e=Q(1,10000);a=Q(1,2);b=1-e*e
b2=e*a+(1-e)*b
b3=e*a**3+(1-e)*b**3
delta=1-b2;gap=b3-b2**3
assert gap==e*(1-e)*(b-a)**2*((2-e)*b+(1+e)*a)
assert 0<delta<=e and b2>=Q(1,2)
assert gap>e/4
margin=gap**2-324*delta**3
assert margin>0
# A strictly positive COMMON realization of the same all-cap kernel.
c=(1+b)/2;x=a/c;y=b/c
assert 0<x<1 and 0<y<1 and 0<c<1 and 0<e<1
assert c*x==a and c*y==b
# Both padding survivals are the positive algebraic root of z^2-c=0.
out={'status':'EXACT_RATIONAL_SLOT_NO_CONTROL_PASS',
     'source_bound':'D3=9; b2>=1/2 implies (b3-b2^3)^2<=324(1-b2)^3 for all I words and limits',
     'epsilon':str(e),'ordinary_mixture_survivals':[str(a),str(b)],
     'b2':str(b2),'b3':str(b3),'cubic_gap':str(gap),
     'positive_squared_margin':str(margin),
     'common_word':{'g':str(e),'arm_x':str(x),'arm_y':str(y),'both_padding_survivals':'positive square root of '+str(c)},
     'scope':'NO for the declared private I-slot kernel image. Hidden slot coordinates and all-core coverage are not inferred.'}
Path(__file__).with_name('NONLINEAR-SLOT-NO-CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
