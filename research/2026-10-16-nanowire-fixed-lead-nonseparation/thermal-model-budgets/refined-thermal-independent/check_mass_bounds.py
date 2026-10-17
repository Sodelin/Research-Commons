from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json,hashlib,sys
if sys.flags.optimize: raise RuntimeError('Assertions required')
D=Path(__file__).resolve().parent.parent;P=D/'refined-thermal-execution'
r=json.loads((P/'RESULT.json').read_text());c=json.loads((P/'CDF-RESULT.json').read_text())
assert hashlib.sha256((P/'RESULT.json').read_bytes()).hexdigest()==c['source_result_sha256']
kb=F(1380649,10**29)/F(1602176634,10**31);theta=kb/1000
assert F(r['theta'])==theta and F(r['temperature_K'])==F(1,1000) and F(r['eta'])==F(1,1000) and F(r['drift'])==0
X=F(r['domain']); assert X==F(1,1000)
def cdf80(x):
 v=abs(x)/theta; terms=[v**j/F(factorial(j)) for j in range(81)];lo=sum(terms); assert v<82
 hi=lo+terms[-1]*v/81/(1-v/82)
 return (lo/(1+lo),hi/(1+hi)) if x>=0 else (1/(1+hi),1/(1+lo))
cells=sorted(r['cells'],key=lambda a:F(a['lo'])); recorded={(F(a['lo']),F(a['hi'])):F(a['contribution_upper']) for a in c['cells']}
assert len(recorded)==len(cells)==64
last=-X;total=F(0)
for a in cells:
 lo,hi,u=F(a['lo']),F(a['hi']),F(a['upper']); assert lo==last and lo<hi and 0<=u<=4;last=hi
 assert F(a['center_beta'])>F(1,2) and F(a['beta_error'])==F(1,2**48)
 uppermass=cdf80(hi)[1]-cdf80(lo)[0]; assert u*uppermass<=recorded[(lo,hi)]
 total+=recorded[(lo,hi)]
assert last==X and total==F(c['inside_upper'])
v=X/theta;tail=2/(1+sum(v**j/F(factorial(j)) for j in range(25)))
assert tail==F(r['tail_probability_upper'])==F(c['tail_probability_upper'])
f0=F(json.loads((D/'thermal-budget-execution/PRIOR-CONDUCTANCE-RESULT.json').read_text())['values']['plus']['g_LL']['upper'])
warm=min(F(4),total+4*tail);Q=1-2*warm-f0-2*F(r['eta'])
assert warm==F(c['warm_upper']) and Q==F(c['Q_lower']) and Q>0
print('PASS independently authored 80-term Fermi-mass check: 64 cells, exact tail, SI conversion, full-budget target.')
print('Warm upper display:',float(warm),'Q lower display:',float(Q))
