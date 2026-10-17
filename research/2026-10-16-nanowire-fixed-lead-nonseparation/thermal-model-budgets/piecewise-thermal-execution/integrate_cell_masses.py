from fractions import Fraction as F
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
raw=(P/'RESULT.json').read_bytes();d=json.loads(raw);theta=F(d['theta']);cells=sorted(d['cells'],key=lambda c:F(c['lo']));X=F(d['domain'])
assert F(cells[0]['lo'])==-X and F(cells[-1]['hi'])==X
inside=F(0);out=[];last=-X
for c in cells:
 lo,hi,u=map(F,(c['lo'],c['hi'],c['upper']));assert lo==last and hi>lo and 0<=u<=4;last=hi
 if 'witness' in c:assert hashlib.sha256((P/c['witness']).read_bytes()).hexdigest()==c['witness_sha256']
 def cdf_bounds(x):
  v=abs(x)/theta;t=s=F(1)
  for j in range(1,61):t*=v/j;s+=t
  assert v<62
  rem=(t*v/61)/(1-v/62); upper=s+rem
  if x>=0:return s/(1+s),upper/(1+upper)
  return 1/(1+upper),1/(1+s)
 mass=cdf_bounds(hi)[1]-cdf_bounds(lo)[0];term=u*mass
 scale=10**18;term=F((term.numerator*scale+term.denominator-1)//term.denominator,scale)
 inside+=term;out.append({'lo':str(lo),'hi':str(hi),'contribution_upper':str(term)})
prior=json.load(open(P.parent/'thermal-budget-execution/PRIOR-CONDUCTANCE-RESULT.json'));f0=F(prior['values']['plus']['g_LL']['upper']);tail=F(d['tail_probability_upper']);warm=min(F(4),inside+4*tail);Q=1-2*warm-f0-2*F(d['eta'])
r={'status':'POSITIVE_CONDITIONAL_ON_INPUT_CELL_CERTIFICATES' if Q>0 else 'INCONCLUSIVE','source_result_sha256':hashlib.sha256(raw).hexdigest(),'temperature_K':d['temperature_K'],'inside_upper':str(inside),'tail_probability_upper':str(tail),'warm_upper':str(warm),'Q_lower':str(Q),'cells':out,'displays':{'inside':float(inside),'warm':float(warm),'Q_lower':float(Q)}}
(P/'CDF-RESULT.json').write_text(json.dumps(r,indent=2)+'\n');print(r['status'],r['displays'])
