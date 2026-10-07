from fractions import Fraction as F
from pathlib import Path
import hashlib,json,sys,time
start=time.monotonic()
lam=[0,1,3,6,10,15,21]
D=2**20
exponents=[D*(F(n+2)-F(1,2**(n-1))) for n in lam[1:]]
assert all(x.denominator==1 for x in exponents)
assert exponents==[2097152,4980736,8355840,12580864,17825728,24117247]
assert D*F(1,2**195)==F(1,2**175)
assert exponents[1]!=3*exponents[0]
rows=[[F(1)]]
for m in range(2,8):
 rate=F(m*(m-1),2)
 row=[rate*c/(rate-F(lam[j])) for j,c in enumerate(rows[-1])]
 row.append(F(2,m*(m+1))-sum(row)); rows.append(row)
expected=[['1'],['1','-2/3'],['1','-1','1/6'],['1','-6/5','1/3','-1/30'],['1','-4/3','10/21','-1/12','1/140'],['1','-10/7','25/42','-5/36','3/140','-1/630'],['1','-3/2','25/36','-7/36','9/220','-1/180','1/2772']]
assert rows==[[F(x) for x in row] for row in expected]
bvals=[sum(c*F(1,2)**n for c,n in zip(row,lam)) for row in rows[1:3]]
assert bvals==[F(2,3),F(25,48)]
for q in [2,3,7,19]:
 L=q**20
 assert all((L*(F(n)+sum(F(1,q**j) for j in range(n)))).denominator==1 for n in lam[1:])
output={'status':'PASS_NEW_COMPACT_RATIONAL_ARITHMETIC_ONLY','code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'cleared_exponents':list(map(int,exponents)),'loss_identity':'2^20 * 2^-195 = 2^-175','nonbaseline_exponents':[int(exponents[1]),int(3*exponents[0])],'monophyly_coefficients':expected,'B_calibration':list(map(str,bvals)),'additional_denominator_checks_q':[2,3,7,19],'not_executed':['expanded rational inputs','small-loss certificate regeneration','source realization','RCF or source census'],'seconds':time.monotonic()-start,'python':sys.version}
f=Path('rational-arithmetic-result.json');assert not f.exists();f.write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output,indent=2))
