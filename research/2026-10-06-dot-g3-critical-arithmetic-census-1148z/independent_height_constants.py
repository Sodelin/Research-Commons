"""Fresh independent integer verification of universal height constants only."""
import resource
resource.setrlimit(resource.RLIMIT_CPU,(5,5))
resource.setrlimit(resource.RLIMIT_AS,(128*1024**2,128*1024**2))
import json,hashlib,time,sys,math
from pathlib import Path
start=time.monotonic();root=Path(__file__).resolve().parent
src=root.parent/'g3-astra-continuous-20261006-0732z/providers/symbolic-normal-pilot.json'
pin='cc57db65563ac4a7e2f5bf9581b8b75803f2052a49d19442f5e756a0f82996e3'
raw=src.read_bytes();assert hashlib.sha256(raw).hexdigest()==pin
obj=json.loads(raw);lam=[1,3,6,10,15,21];assert obj['lambda']==lam
rows=[[int(x) for x in row] for row in obj['B_coefficients_descending']]
assert [len(row)-1 for row in rows]==[49,49,46,42,32,20]
assert [row[-1] for row in rows]==[0,0,0,-6,11,-5]
norms=[sum(abs(x) for x in row) for row in rows]
S=sum(norms);Sl=sum(n*v for n,v in zip(lam,norms))
L=max(1,2*3**5*S,5*3**5*Sl)
c=(2*math.factorial(9)*L**9).bit_length();ell=(2*L).bit_length()
# Independent monic synthetic division of P6(X,1) at X=-2.
a=[1,2,3,4,5];horner=[a[0]]
for x in a[1:]:horner.append(x-2*horner[-1])
assert horner[:-1]==[1,0,3,-2] and horner[-1]==9
q_slope=9*49;p_slope=49+56*q_slope
factor_slope=44*p_slope+42*q_slope
factor_constant=44*(56*c+ell)+42*c+44
assert (L,c,ell,p_slope,factor_slope,factor_constant)==(12377326500,322,35,24745,1107302,808516)
assert hashlib.sha256(src.read_bytes()).hexdigest()==pin
out={'status':'PASS_NEW_INDEPENDENT_UNIVERSAL_INTEGER_CONSTANTS','new_execution':True,
'input_sha256':pin,'input_B_degrees':[len(row)-1 for row in rows],
'endpoint_projective_row':[row[-1] for row in rows],'coefficient_l1_norms':norms,'S':S,'S_lambda':Sl,
'L':L,'log_bound_c':c,'log_bound_ell':ell,'P6_div_P3_quotient_descending':horner[:-1],
'P6_div_P3_remainder':horner[-1],'resultant_r_degree_upper':9*49,
'resultant_q_degree_upper':4*56+5*55,'pair_field_degree_upper_for_rational_r':5*(4*56+5*55),
'q_height_log_B_coefficient':q_slope,'p_height_log_B_coefficient':p_slope,
'one_factor_normalized_height_log_B_coefficient':factor_slope,
'one_factor_normalized_height_constant':factor_constant,'seconds':time.monotonic()-start,
'python':sys.version,'limits':{'cpu_seconds':5,'address_space_bytes':128*1024**2,'wall_seconds':10},
'scope':'Only universal integer coefficient norms, degree arithmetic, endpoint row and one synthetic polynomial division. No old symbolic replay, observation-dependent height bound, residue census, root isolation, QE or source decision.'}
with (root/'independent-height-constant-result.json').open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
