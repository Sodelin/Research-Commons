"""Independent integer replay of saved witness, without NumPy or matrix inversion."""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import json,hashlib,sys
if sys.flags.optimize: raise RuntimeError('No optimized mode')
p=Path(__file__).resolve().parent.parent/'thermal-budget-execution'
r=json.loads((p/'RESULT.json').read_text()); z=json.loads((p/'inverse_gaussian_integer.json').read_text()); k=json.loads((p/'scaled_K_rows.json').read_text())
for name,h in r['artifact_sha256'].items(): assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h
assert hashlib.sha256((p/'certify_inverse.py').read_bytes()).hexdigest()==r['source_sha256']
assert hashlib.sha256((p/'PRIOR-CONDUCTANCE-RESULT.json').read_bytes()).hexdigest()==r['prior_conductance_sha256']=='9e1eb9198562c8696d005819c6ffb8aa40d236c5afa4d3ff80d8ce3b96906647'
n=240; d=k['denominator']; s=z['denominator']; assert d==25000000000000 and s==2**48
# Reconstruct every Hamiltonian entry independently from the published block convention.
ons=lambda a:[[a,F(1,5),2,0],[F(1,5),-a,0,2],[2,0,a,F(1,5)],[0,2,F(1,5),-a]]
t=F(501643,20000); l=F(5,2)
hop=[[-t,0,-l,0],[0,t,0,l],[l,0,-t,0],[0,-l,0,t]]
expected=[]
for i in range(n):
 site,u=divmod(i,4); a=F(1000) if site in (0,59) else F(1234321162378001,d); row=[]
 for j in range(n):
  sj,v=divmod(j,4)
  h=ons(a)[u][v] if sj==site else hop[u][v] if sj==site+1 else hop[v][u] if sj==site-1 else 0
  re=-F(h)*d; im=d if i==j and site in (0,59) else 0
  assert re.denominator==1
  if re or im: row.append([j,int(re),im])
 expected.append(row)
assert k['rows']==expected
zr=z['real'];zi=z['imag']; assert len(zr)==len(zi)==n and all(len(v)==n for v in zr+zi)
rsq=0
for i,row in enumerate(expected):
 for j in range(n):
  re=-(d*s if i==j else 0); im=0
  for h,a,b in row:
   re+=a*zr[h][j]-b*zi[h][j]; im+=a*zi[h][j]+b*zr[h][j]
  rsq+=re*re+im*im
zsq=sum(v*v for mat in (zr,zi) for row in mat for v in row)
assert rsq==int(r['residual_squared_integer']) and zsq==int(r['inverse_squared_integer'])
cr=isqrt(rsq)+int(isqrt(rsq)**2<rsq);cz=isqrt(zsq)+int(isqrt(zsq)**2<zsq)
assert cr==int(r['residual_ceil_sqrt']) and cz==int(r['inverse_ceil_sqrt'])
e=F(cr,d*s); zn=F(cz,s); assert e<1
rho=(1-e)/zn; assert rho==F(r['rho_lower'])
W=rho/2;L=4+32/rho**2;theta=rho**2/10000;pu=2*theta/W;eta=F(1,1000)
assert 0<W<1 and 0<pu<1
prior=json.loads((p/'PRIOR-CONDUCTANCE-RESULT.json').read_text()); assert F(prior['values']['plus']['g_LL']['upper'])<F(1,250)
warm=F(1,250)+2*L*theta+4*pu
q=1-(warm+2*eta+2*L*theta)/(1-pu)
assert warm==F(r['warm_conductance_upper']) and q==F(r['Q_lower']) and q>F(98119,100000)
kb=F(1380649,10**29)/F(1602176634,10**31);temp=theta/kb; assert temp==F(r['temperature_K'])
print('PASS: exact published-model reconstruction, full integer residual, witness hashes, rational thermal budget')
print('rho =',rho,'; decimal display',float(rho))
print('Q lower =',q,'; decimal display',float(q))
print('temperature K display =',float(temp))
print('No numerical inverse proposal or NumPy was executed by this independent checker.')
# Independent rational check of the appended 1 mK window-bound obstruction.
th_mk=kb/F(1000)
assert th_mk>=rho and 16*eta*th_mk>rho*rho
print('PASS: appended bound limitation at >=1 mK; squared lower bound display',float(16*eta*th_mk/rho**2))
