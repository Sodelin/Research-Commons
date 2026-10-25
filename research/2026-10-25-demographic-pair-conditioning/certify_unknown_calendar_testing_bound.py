"""Two-source finite-N impossibility controls with exact outward rational intervals."""
from fractions import Fraction as F
from pathlib import Path
import json
import certify_unknown_calendar_inverse as ci
I=ci.I
C=[[F(x,64) for x in row] for row in [[27,-81,81,-27],[27,27,-135,81],[9,45,27,-81],[1,9,27,27]]]
def probs(z):
 v=[I(1)]+[ci.phi([I(x) for x in z],a) for a in [1,2,3]]
 return [sum(row[r]*v[r] for r in range(4)) for row in C]
def bound(z0,z1,eta,label):
 assert max(abs(x-y) for x,y in zip(z0,z1))>=2*eta
 p,q=probs(z0),probs(z1)
 chi=F(0)
 for pi,qi in zip(p,q):
  assert pi.lo>0
  chi+=(qi-pi).absmax()**2/pi.lo
 # Simple outward readable decimal bound, retaining enough significant digits.
 scale=10**25;chi=F((chi*scale).__ceil__(),scale)
 threshold=F(81,50)/chi # 2*(1-2*0.05)^2 / chi-square upper bound
 return {'label':label,'source0':list(map(str,z0)),'source1':list(map(str,z1)),'eta':str(eta),'source0_probability_intervals':[v.out() for v in p],'source1_probability_intervals':[v.out() for v in q],'chi_square_upper':str(chi),'necessary_loci_at_least':threshold.__ceil__(),'derivation':'KL(P1||P0)<=chi_square; TV(product)<=sqrt(N chi_square/2); disjoint strict eta-success balls require TV>=9/10 for 95% accuracy at BOTH sources.'}
c=[F(1),F(2),F(1)]
large=[F('1.0033542746'),F('2.2'),F('1.0735205285')]
# Near-center efficient nuisance adjustment, rational approximate Fisher direction.
# Chosen direction only motivates pair; bound uses exact laws, not Fisher asymptotics.
b=F(1,16384)
w=[F('0.02055418'),F(1),F('0.41996702')]
small=[c[i]+b*w[i] for i in range(3)]
assert all(abs(small[i]-c[i])<=b for i in range(3))
rows=[bound(c,large,F(1,10),'broad separated chart, eta=0.1'),bound(c,small,b/2,'same tiny box and target as local upper certificate')]
out={'status':'passed exact interval two-point controls; testing implication is written proof','rows':rows,'limitations':'The large rival was numerically selected then rationally rounded; optimality of rival not needed or asserted. Small direction was selected using floating Fisher information; all final source probabilities and chi-square bounds are rational-interval checked.'}
Path(__file__).with_name('unknown-calendar-testing-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
for r in rows:print(r['label'],r['chi_square_upper'],r['necessary_loci_at_least'])
