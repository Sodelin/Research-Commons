from pathlib import Path
from fractions import Fraction as F
import json,hashlib,datetime,sys
sys.set_int_max_str_digits(0)
BASE=Path('/workspace/Research-Commons/research/2026-10-08-codex-g3-g4-coordinated-1000z')
path=BASE/'g4-forest/EXACT-LOCAL-MARGIN-v3.json';d=json.loads(path.read_text())
b=json.loads((BASE/'g4-forest/ACTUAL-BANK-JACOBIAN-v2.json').read_text());P=b['prime']
r=list(map(F,d['all20_exact_response_residual']));ell=list(map(F,d['rational_dual_covector_all20']));proj=list(map(F,d['exact_dual_jacobian_columns_36']))
w=[F(2,125),F(33,1000),F(49,750),F(19,1000)]*9
lhs=abs(sum((x*y for x,y in zip(ell,r)),F(0)));rhs=sum((x*abs(y) for x,y in zip(w,proj)),F(0))
assert lhs==F(d['abs_dual_residual']) and rhs==F(d['sum_w_abs_dual_jacobian'])
assert lhs/rhs==F(d['required_relative_infinity_radius_lower_bound_exact']) and lhs>818*rhs>0
assert d['strict_integer_radius_lower_bound']==818
q=lambda v:v.numerator*pow(v.denominator,-1,P)%P
assert [q(x) for x in r]==[(x-y)%P for x,y in zip(b['base_response_mod_prime'],b['ordinary_target_mod_prime'])]
assert [q(x) for x in proj]==[sum(q(x)*y for x,y in zip(ell,c))%P for c in zip(*b['full_20_by_36_jacobian_mod_prime'])]
result={'schema':'independent-static-rational-dual-review-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS_STATIC_CERTIFICATE_ARITHMETIC_ONLY','executed_review_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'input_bytes':len(path.read_bytes()),'scope':'exact serialized Fraction arithmetic only; no source/helper/scientific module, Newton, QE, compiler or source solver execution','exact_dual_residual_and_weighted_derivative_sum_match':True,'serialized_full_residual_modularly_matches_frozen_bank':True,'serialized_dual_jacobian_modularly_matches_frozen_bank':True,'exact_ratio_strictly_exceeds':818,'statement':'Every exact solution of the initial fixedbank complete linear Newton equation requires relative infinity displacement >818. This does not exclude nonlinear moves or larger one-sided positive moves.'}
(BASE/'review/G4-LOCAL-DUAL-STATIC-VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'strict_integer_bound':818}))
