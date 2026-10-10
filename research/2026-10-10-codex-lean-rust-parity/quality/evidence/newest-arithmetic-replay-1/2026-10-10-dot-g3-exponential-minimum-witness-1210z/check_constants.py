from fractions import Fraction as F
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
raw=(P/'paired-normal-certificate.json').read_bytes();j=json.loads(raw)
k={x:F(v) for x,v in j['constants'].items()}
lam=(1,3,6,10,15,21)
c0=[F(x) for x in j['normal_records']['F0']['c']]+[F(0),F(0)]
c1=[F(x) for x in j['normal_records']['F1']['c']]
for c in (c0,c1):
 assert sum(l*x for l,x in zip(lam,c))==0
 assert sum(x*(1-F(1,2)**l) for l,x in zip(lam,c))==0
u=F(1,2)+k['root_interval_half_width']
kap=min(k['outside_U_F0_lower_bound']/12,F(j['normal_records']['F0']['F_second_derivative_at_one'])*k['Q']**3/12)
C0=min(k['C_star'],k['gamma']*(1-u)/(4*k['B1']*(k['B0']/k['delta'])**2))
K=2*k['B1']/k['delta']**2
Lc=6+k['B0']*k['p0']/kap
assert min(kap,C0,K,Lc)>0
# Choose a fixed rational dyadic base; do not expand its large fixed powers.
b=1
while F(2)**(23-b)>C0: b+=1
eta=F(1,2**b);Dlow=F(5,4)*2**20*eta
assert 2**22*eta<=C0/2
Eexp=[2**20*l+2**21-2**(21-l) for l in lam]
assert all(isinstance(e,int) and e>0 for e in Eexp)
A0=6*sum(abs(x) for x in c0);A1=6*sum(abs(x) for x in c1)
CE=A1+K*A0*A0
# Limiting three-head derivative matrix, columns D(r), D'(r).
rs=(F(1,2),F(1,3),F(1,4))
J=[[v for r in rs for v in (1-r**l,-l*r**(l-1))] for l in lam]
def inv(A):
 n=len(A);X=[list(row)+[F(i==j) for j in range(n)] for i,row in enumerate(A)]
 for z in range(n):
  piv=next(i for i in range(z,n) if X[i][z]);X[z],X[piv]=X[piv],X[z]
  t=X[z][z];X[z]=[a/t for a in X[z]]
  for i in range(n):
   if i!=z:
    t=X[i][z];X[i]=[a-t*b for a,b in zip(X[i],X[z])]
 return [row[n:] for row in X]
Ji=inv(J);Jnorm=max(sum(abs(x) for x in row) for row in Ji)
for A,B in ((J,Ji),(Ji,J)):
 assert all(sum(A[i][s]*B[s][z] for s in range(6))==F(i==z) for i in range(6) for z in range(6))
eth=min(F(1,2),1/(264*Jnorm),C0/16,kap*Dlow/(2*A0))
k0=1
while F(1,2**k0)>eth:k0+=1
G=k['gamma']*Dlow**3/(16*Lc**3*CE)
shift=0
while F(1,4**shift)>G:shift+=1
# Every k>=k0 has n^2>=G 2^k, hence n>=2^(k/2-shift).
print('PASS frozen normal neutrality and dyadic residue equations')
print('PASS exact positive count constants and fixed rational NO loss gate')
print('PASS three-head limiting Jacobian inverse on both sides')
print('base dyadic exponent b =',b)
print('uniform perturbation index k0 =',k0)
print('minimum count n >= 2^(k/2 - %d)'%shift)
print('for k >= %d, n >= 2^(k/4)'%max(k0,4*shift))
print('fixed target moment exponent vector =',Eexp)
print('No fixed target numerators, variable target inputs, or realizing graphs expanded.')
R={'provider_sha256':hashlib.sha256(raw).hexdigest(),'lambda':lam,'ratios':[str(x) for x in rs],'base_dyadic_exponent':b,'fixed_target_exponents':Eexp,'k0':k0,'square_root_shift':shift,'k_for_quarter_exponent':max(k0,4*shift),'count_constants':{name:str(val) for name,val in {'kappa':kap,'C0':C0,'K_count':K,'L_count':Lc,'D_lower':Dlow,'A0':A0,'A1':A1,'C_E':CE,'J_inverse_norm':Jnorm,'epsilon_threshold':eth,'G_lower':G}.items()},'limiting_jacobian':[[str(x) for x in row] for row in J],'limiting_jacobian_inverse':[[str(x) for x in row] for row in Ji]}
(P/'derived-constants.json').write_text(json.dumps(R,indent=2)+'\n')
