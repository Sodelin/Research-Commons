"""Synthetic polynomial/bracket certificate; the CAS proposes, Lean validates."""
import hashlib, json, os, resource, subprocess, time
from pathlib import Path
import sympy as sp

root=Path(__file__).resolve().parent
x,y=sp.symbols('x y'); t=time.perf_counter()
expanded=sp.expand((x+y)**3)
coeffs=[int(sp.Poly(expanded,x,y).coeff_monomial(m)) for m in [x**3,x**2*y,x*y**2,y**3]]
generation=time.perf_counter()-t
template='''import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
namespace SyntheticCertificate
theorem expanded_cube (x y : ℚ) :
    (x+y)^3 = COEFFICIENTS := by ring
theorem root_bracket (x : ℝ) (hx : 0 ≤ x) (hs : x^2 = 2) :
    (141421356 : ℝ)/100000000 < x ∧ x < (141421357 : ℝ)/100000000 := by
  constructor
  · by_contra h
    have hlt : x ≤ (141421356 : ℝ)/100000000 := le_of_not_gt h
    have hp : 0 ≤ (((141421356 : ℝ)/100000000)-x)*(((141421356 : ℝ)/100000000)+x) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  · by_contra h
    have hlt : (141421357 : ℝ)/100000000 ≤ x := le_of_not_gt h
    have hp : 0 ≤ (x-((141421357 : ℝ)/100000000))*(x+((141421357 : ℝ)/100000000)) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
#print axioms expanded_cube
#print axioms root_bracket
end SyntheticCertificate
'''
def polynomial(cs): return f'{cs[0]}*x^3 + {cs[1]}*x^2*y + {cs[2]}*x*y^2 + {cs[3]}*y^3'
good=root/'SyntheticCertificate.lean';bad=root/'CorruptCertificate.lean'
good.write_text(template.replace('COEFFICIENTS',polynomial(coeffs)))
corrupt=coeffs[:];corrupt[1]+=1
bad.write_text(template.replace('COEFFICIENTS',polynomial(corrupt)))
base=Path('/workspace/shared/lean-formalization');lean=base/'tooling/lean-4.33.1-linux/bin/lean'; mathlib=base/'build/mathlib'
env=os.environ.copy();env['LEAN_PATH']=':'.join(str(p) for p in [mathlib/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (mathlib/'.lake/packages').iterdir()])
receipt={'input_class':'synthetic/public algebra, no G theorem','generation_seconds':generation,'sympy':sp.__version__,'generated_coefficients':coeffs,'compiler_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'mathlib_commit':'0df444a360eaa60ab8c11dca51a86af692955474','compile_parameters':['-j1','-M2048'],'cases':[]}
for p in [good,bad]:
 if p.with_suffix('.olean').exists(): p.with_suffix('.olean').unlink()
 t=time.perf_counter()
 try:
  cp=subprocess.run([str(lean),'-j1','-M2048','-o',str(p.with_suffix('.olean')),str(p)],env=env,capture_output=True,text=True,timeout=20)
  code=cp.returncode;log=cp.stdout+cp.stderr
 except subprocess.TimeoutExpired as e: code=124;log='TIMEOUT'
 seconds=time.perf_counter()-t;p.with_suffix('.log').write_text(log)
 receipt['cases'].append({'source':p.name,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'compile_exit_code':code,'elapsed_seconds':seconds,'log_sha256':hashlib.sha256(log.encode()).hexdigest(),'object_exists':p.with_suffix('.olean').exists(),'children_cumulative_maxrss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'axiom_lines':[s for s in log.splitlines() if 'axioms' in s]})
receipt['expected_outcomes_pass']=(receipt['cases'][0]['compile_exit_code']==0 and receipt['cases'][0]['object_exists'] and all('sorryAx' not in s and 'ofReduceBool' not in s for s in receipt['cases'][0]['axiom_lines']) and receipt['cases'][1]['compile_exit_code']!=0 and not receipt['cases'][1]['object_exists'])
(root/'certificate-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
