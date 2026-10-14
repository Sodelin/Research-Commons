"""Exact transcription controls; not a source compiler or universal G4 proof."""
from fractions import Fraction as F
import json
from pathlib import Path

def add(a,b):
    return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0)) for i in range(max(len(a),len(b)))]
def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out

def scale(a,k):return [k*x for x in a]
def value(a,x):return sum((c*x**i for i,c in enumerate(a)),F(0))

rho=F(1,2);g=F(2,3);a=F(3,4);r=F(1,2)
bare_b2=g*g*rho+2*g*(1-g)+(1-g)**2*rho
v=(2-3*rho+rho**3)/6
bare_c=2*(g*g*(1-g)**2*(1-rho)**2-g**3*(1-g)*v-g*(1-g)**3*v)
b2=a*r*bare_b2;c=a**6*r*bare_c
assert b2==F(13,48)
assert c==F(-3,32768)
ratio=c/b2
assert ratio==F(-9,26624)
p=add([0,F(1,5),0,F(-1,3),0,0,F(2,15)],scale([0,1,0,0,0,0,-1],F(3,5)*ratio))
Q=[3,6,4,2];R=[1,1,1,1,1]
bracket=add(scale(mul([1,-1],Q),F(1,15)),scale(R,F(-27,133120)))
assert p==mul([0,1,-1],bracket)
assert value(p,F(1))==0
assert -sum((i*x for i,x in enumerate(p)),F(0))==F(-27,26624)
assert F(1,5000)<F(27,133120)
s=F(9999,10000)
assert value(p,s)<0
jacobian=-(1/rho+2*rho/(rho*rho+3)-3/(1+rho))
assert jacobian==F(-4,13)
receipt={"schema":"g4_finite_bridge_exact_controls_v1","status":"PASS","assertions":9,
"target_b2":str(b2),"target_c":str(c),"target_c_over_b2":str(ratio),
"target_conjugate_named_forest_probability_polynomial":[str(x) for x in p],
"time_derivative_at_zero":str(F(-27,26624)),"strict_interval_survival_lower":str(F(4999,5000)),
"rational_survival_control":str(s),"rational_coordinate_value":str(value(p,s)),
"prefix_shift_jacobian":str(jacobian),"formal_polynomial_factorization_exact":True,
"source_compiler_executed":False,"lean_executed":False,"all_orders_occupation_classification_proved_by_test":False,
"negative_conjugate_is_admitted_rival":False,"g4_master_closed":False}
text=json.dumps(receipt,indent=2,sort_keys=True)+"\n"
Path(__file__).with_name("evidence").joinpath("EXACT-CONTROLS.json").write_text(text)
print(json.dumps({"status":"PASS","assertions":9,"g4_master_closed":False},sort_keys=True))
