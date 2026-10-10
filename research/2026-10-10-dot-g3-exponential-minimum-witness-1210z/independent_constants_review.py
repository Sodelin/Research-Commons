from fractions import Fraction as Q
from pathlib import Path
import json
p=Path(__file__).resolve().parent
old=json.loads((p/'paired-normal-certificate.json').read_text()); got=json.loads((p/'derived-constants.json').read_text())
cs={a:Q(b) for a,b in old['constants'].items()};L=[1,3,6,10,15,21]
a=[Q(v) for v in old['normal_records']['F0']['c']]+[Q(0)]*2
b=[Q(v) for v in old['normal_records']['F1']['c']]
for row in [a,b]:
 assert sum(row[i]*L[i] for i in range(6))==0
 assert sum(row[i]*(1-Q(1,2)**L[i]) for i in range(6))==0
kap=min(cs['outside_U_F0_lower_bound']/12,Q(old['normal_records']['F0']['F_second_derivative_at_one'])*cs['Q']**3/12)
C=min(cs['C_star'],cs['gamma']*(Q(1,2)-cs['root_interval_half_width'])/(4*cs['B1']*(cs['B0']/cs['delta'])**2))
K=2*cs['B1']/cs['delta']**2; LL=6+cs['B0']*cs['p0']/kap
A0=6*sum(map(abs,a));A1=6*sum(map(abs,b));CE=A1+K*A0**2
DL=Q(5,4)*2**20*Q(1,2**196)
G=cs['gamma']*DL**3/(16*LL**3*CE)
assert 0<C<=cs['p0']*(1-cs['Q'])
assert Q(2**22,2**196)<=C/2
assert G>=Q(1,2**580)
J=[[entry for r in [Q(1,2),Q(1,3),Q(1,4)] for entry in [1-r**l,-l*r**(l-1)]] for l in L]
Inv=[[Q(x) for x in row] for row in got['limiting_jacobian_inverse']]
for X,Y in [(J,Inv),(Inv,J)]:
 for i in range(6):
  for j in range(6):
   assert sum(X[i][z]*Y[z][j] for z in range(6))==Q(i==j)
IJ=max(sum(map(abs,row)) for row in Inv)
assert Q(1,2**280)<=min(Q(1,2),Q(1)/(264*IJ),C/16,kap*DL/(2*A0))
for name,value in {'kappa':kap,'C0':C,'K_count':K,'L_count':LL,'D_lower':DL,'A0':A0,'A1':A1,'C_E':CE,'J_inverse_norm':IJ,'G_lower':G}.items():
 assert Q(got['count_constants'][name])==value
E=[2**20*l+2**21-2**(21-l) for l in L]
assert E==[2097152,4980736,8355840,12580864,17825728,24117247]
assert sum(E)==69957567 and sum(L)==56 and sum(l+3 for l in L)==74
assert 196*sum(E)+5*56+1==13711683413
assert 12*4*74==3552 and 2*3552==7104
bits=lambda n:max(1,n.bit_length())
enc=lambda n,d:2*bits(n)+2*bits(d)+2
assert [enc(n,d) for n,d in [(2,3),(1,3),(25,48),(23,48)]]==[10,8,24,24]
assert 12*2+sum(enc(n,d) for n,d in [(2,3),(1,3),(25,48),(23,48)])==90
print('PASS independently recomputed normal/count constants and fixed rational NO loss inequality')
print('PASS directly reconstructed source Jacobian and verified both inverse products')
print('PASS exact k>=280 gates and G>=2^-580, without expanding target powers')
print('PASS all fixed exponents, denominator-bit coefficient3552, exponent divisor7104 and encoding constants')
