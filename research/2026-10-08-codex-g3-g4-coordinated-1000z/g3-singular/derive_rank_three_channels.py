from fractions import Fraction as F
from pathlib import Path
import json,hashlib,datetime,time
root=Path(__file__).resolve().parents[3]
out=Path(__file__).resolve().parent
source=root/'research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/RATIONAL-INPUT-CONSEQUENCES.md'
exponents=[1,3,6,10,15,21]
A=[[-F(2,3),0,0,0,0,0],[-1,F(1,6),0,0,0,0],[-F(6,5),F(1,3),-F(1,30),0,0,0],[-F(4,3),F(10,21),-F(1,12),F(1,140),0,0],[-F(10,7),F(25,42),-F(5,36),F(3,140),-F(1,630),0],[-F(3,2),F(25,36),-F(7,36),F(9,220),-F(1,180),F(1,2772)]]
A=[[F(x) for x in row] for row in A]
started=datetime.datetime.now(datetime.timezone.utc).isoformat();start=time.monotonic()
rows=[row+[F(int(i==j)) for j in range(6)] for i,row in enumerate(A)]
for i in range(6):
    pivot=rows[i][i]
    assert pivot
    rows[i]=[v/pivot for v in rows[i]]
    for j in range(6):
        if i!=j:
            coefficient=rows[j][i];rows[j]=[v-coefficient*w for v,w in zip(rows[j],rows[i])]
C=[row[6:] for row in rows]
checks={}
for i in range(6):
    for j in range(6):
        checks[f'inverse_entry_{i}_{j}']=sum(C[i][k]*A[k][j] for k in range(6))==int(i==j)
def rational(x):return str(x.numerator) if x.denominator==1 else f'{x.numerator}/{x.denominator}'
channels=[]
for exponent in [1,10,21]:
    index=exponents.index(exponent);coeff=C[index];offset=-sum(coeff);K=1+abs(offset)+sum(abs(x) for x in coeff)
    channels.append({'moment_exponent':exponent,'affine_recovery_constant':rational(offset),'coefficients_for_monophyly_indicators_A2_through_A7':[rational(x) for x in coeff],'K':rational(K),'channel_probability_formula':'1/2 + (constant + sum coefficients[k]*I_A(k+2))/(2*K)','source_mean_moment_formula':'2*K*(observed_probability-1/2)'})
    checks[f'exponent_{exponent}_strict_channel_margin']=K>abs(offset)+sum(abs(x) for x in coeff)
record={'schema':'g3-rank3-channel-coefficient-derivation-v1','claim_tier':'exact rational arithmetic of inherited affine transform only; not source simulation or whole-source verification','started_utc':started,'elapsed_seconds':time.monotonic()-start,'provider_path':str(source.relative_to(root)),'provider_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'script_path':str(Path(__file__).resolve().relative_to(root)),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'original_exponents':exponents,'original_transform_matrix':[[rational(x) for x in row] for row in A],'inverse_matrix':[[rational(x) for x in row] for row in C],'channels':channels,'checks':checks,'checks_passed':sum(checks.values()),'checks_total':len(checks),'status':'PASS' if all(checks.values()) else 'FAIL','compiler_invocations':0,'solver_invocations':0,'source_instances_executed':0}
(out/'RANK-THREE-CHANNELS.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'channels':channels,'status':record['status'],'checks_passed':record['checks_passed'],'checks_total':record['checks_total']}))
