from fractions import Fraction as F
import json
q=F(1,2)
f=lambda k:(1-q**k)/k
x,y=21,17
G=(f(y)-f(x+y))/x
delta=G-f(x)*f(y)/2
assert delta>0
ratio=f(x)/f(y)
q2=F(3,4)
f2=lambda k:(1-q2**k)/k
assert ratio!=f2(x)/f2(y)
# Exact semigroup composition of normalized gap coefficients, same frame.
# exp(vU) exp(wU): Kac(v+w) = Kac(v)+e^(-(x+y)v)Kac(w)
# + Kab(v)*e^(-yv)*Kbc(w), after normalization in the right-diagonal convention.
# Conjugation uses prefix diagonal: exp(-xv) in ab and exp(-yv) in bc.
# Correct direct composition normalized: Kac(v+w)=Kac(v)+q**(x+y)*Kac(w)+Kab(v)*q**y*Kbc(w).
fprod=lambda k:(1-(q*q2)**k)/k
G2=(f2(y)-f2(x+y))/x
Gprod=(fprod(y)-fprod(x+y))/x
assert Gprod==G+q**(x+y)*G2+f(x)*q**y*f2(y)
result={'status':'PASS exact rational formulas, two positive ordinary survivals','survival':'1/2','x':x,'y':y,'local_excess':str(delta),'profile_ratio_at_half':str(ratio),'profile_ratio_at_three_quarters':str(f2(x)/f2(y)),'semigroup_composition':'PASS','scope':'Formula controls only; all-v strict positivity follows from the hand integral proof; inherited complete-source spectral/projectivity/shape suppliers are not rebuilt.'}
print(json.dumps(result,indent=2))
