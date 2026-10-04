"""Independent fifth-arity sign check on the same contraction box."""
from pathlib import Path
import runpy, json, hashlib
d=runpy.run_path(str(Path(__file__).with_name('independent_check.py')))
Q=d['Q'];S=d['S'];x,y,z,w=d['vs'];fixed=d['fixed'];center=d['center'];rho=d['radius']
def b5(a,b):return (a**10+b**10+5*a**6+5*b**6+10*a**3*b+10*a*b**3)/32
expr=b5(S(fixed[0]),S(fixed[1]))*b5(S(fixed[2]),S(fixed[3]))*b5(x,y)*(z*w)**10-d['pair']**10
lo=[c-rho for c in center];hi=[c+rho for c in center]
a,b=d['interval'](d['poly'](expr),lo,hi)
pa,pb=d['interval'](d['poly'](d['pair']),lo,hi)
assert a<b<0 and pa>0
# Negative numerator: division bounds reverse denominator endpoints.
lower=a/(32*pa)**10;upper=b/(32*pb)**10
assert lower<upper<0
result={'status':'PASS','source_certificate_sha256':hashlib.sha256(d['CERT'].read_bytes()).hexdigest(),
'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'exact_strict_negative':True,'padded_b5_minus_ordinary_display':[float(lower),float(upper)],
'method':'sparse polynomial sign-aware rational monomial enclosure; same certified four-variable box',
'scope':'this three-cell witness only; no new cap search or uniform cutoff'}
Path(__file__).with_name('INDEPENDENT-FIFTH-ARITY-CONTROL.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

