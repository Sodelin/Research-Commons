import json,pathlib,sympy as S
root=pathlib.Path('/workspace/shared/lean-formalization');data=json.load(open(root/'g3-sylvester-transform-certificate.json'))['records'][0]
def leanRat(a):
 q=S.Rational(a)
 return f'({q.p} : ℝ)' if q.q==1 else f'({q.p} : ℝ)/({q.q} : ℝ)'
def table(name,rows,n,m):
 s=f'def {name} (i : Fin {n}) (j : Fin {m}) : ℝ := match i.val,j.val with\n'
 for i,row in enumerate(rows):
  for j,a in enumerate(row):
   if S.Rational(a):s+=f'  | {i},{j} => {leanRat(a)}\n'
 return s+'  | _,_ => 0\n\n'
s='''import G3FixedDegreeResultants
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

noncomputable section
namespace GProgram.G3.AllResidue.SliceThree
open scoped BigOperators
open Polynomial
open GProgram.G3.AllResidue

'''
s+=table('pCoeffTable',data['P_coefficients_ascending_by_free_weight'],5,6)
s+=table('qCoeffTable',data['Q_coefficients_ascending_by_free_weight'],5,5)
s+='''def modelP (x : Fin 5 → ℝ) : Polynomial ℝ :=
  ∑ k : Fin 6, C (∑ i : Fin 5, pCoeffTable i k*x i)*X^k.val

def modelQ (x : Fin 5 → ℝ) : Polynomial ℝ :=
  ∑ k : Fin 5, C (∑ i : Fin 5, qCoeffTable i k*x i)*X^k.val

'''
for i in range(6):
 others=', '.join(str(j) for j in range(6) if j!=i)
 s+=f'theorem erase_univ_{i} : (Finset.univ : Finset (Fin 6)).erase {i} = {{{others}}} := by decide\n'
s+='''
theorem modelP_is_actual_source (x : Fin 5 → ℝ) :
    modelP x = criticalProbabilityPolynomial (fullWeight x) capSevenExponent 3 := by
  apply Polynomial.funext
  intro p
  rw [critical_probability_eval]
  simp only [modelP, Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  norm_num [Fin.sum_univ_succ,pCoeffTable,pCriticalNumerator,
    fullWeight,capSevenExponent,bernoulliFactor,
    erase_univ_0,erase_univ_1,erase_univ_2,erase_univ_3,erase_univ_4,erase_univ_5]
  ring

theorem modelQ_is_actual_source_quotient (x : Fin 5 → ℝ) :
    (1-X)*modelQ x = sourceQProbabilityPolynomial (fullWeight x) capSevenExponent 3 := by
  apply Polynomial.funext
  intro p
  rw [source_q_probability_eval]
  simp only [modelQ, Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,
    Polynomial.eval_X,Polynomial.eval_finsetSum,Polynomial.eval_C,Polynomial.eval_pow]
  norm_num [Fin.sum_univ_succ,qCoeffTable,qCriticalNumerator,
    fullWeight,capSevenExponent,bernoulliFactor,
    erase_univ_0,erase_univ_1,erase_univ_2,erase_univ_3,erase_univ_4,erase_univ_5]
  ring

#print axioms modelP_is_actual_source
#print axioms modelQ_is_actual_source_quotient
end GProgram.G3.AllResidue.SliceThree
'''
(root/'program/G3SylvesterSliceThreeSource.lean').write_text(s)
print('source generated',len(s))
# Assemble the fixed-degree matrices in mathlib's actual Sylvester orientation.
Ps=[[S.Rational(v) for v in row] for row in data['P_coefficients_ascending_by_free_weight']];Qs=[[S.Rational(v) for v in row] for row in data['Q_coefficients_ascending_by_free_weight']]
Sm=[S.Matrix(9,9,lambda i,j:Qs[k][i-j] if j<5 and 0<=i-j<=4 else (Ps[k][i-(j-5)] if j>=5 and 0<=i-(j-5)<=5 else 0)) for k in range(5)]
T=S.Matrix(data['T']).applyfunc(S.Rational);R=S.Matrix(data['R']).applyfunc(S.Rational)
Pre=[T*M for M in Sm];Red=[N*R for N in Pre]
t='''import G3SylvesterSliceThreeSource

noncomputable section
namespace GProgram.G3.AllResidue.SliceThree
open scoped BigOperators
open Polynomial

'''
for name,key in [('T','T'),('Ti','T_inverse'),('R','R'),('Ri','R_inverse')]:t+=table(name,data[key],9,9)
for k in range(5):
 t+=table(f'pre{k}',[[str(v) for v in row] for row in Pre[k].tolist()],9,9)
 t+=table(f'reduced{k}',[[str(v) for v in row] for row in Red[k].tolist()],9,9)
t+='''def pre (x : Fin 5 → ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j => x 0*pre0 i j+x 1*pre1 i j+x 2*pre2 i j+x 3*pre3 i j+x 4*pre4 i j

def reduced (x : Fin 5 → ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j => x 0*reduced0 i j+x 1*reduced1 i j+x 2*reduced2 i j+x 3*reduced3 i j+x 4*reduced4 i j

set_option maxHeartbeats 4000000 in
theorem T_inverse_exact : T*Ti = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [Matrix.mul_apply,Fin.sum_univ_succ,T,Ti,Matrix.one_apply]

set_option maxHeartbeats 4000000 in
theorem R_inverse_exact : R*Ri = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [Matrix.mul_apply,Fin.sum_univ_succ,R,Ri,Matrix.one_apply]

set_option maxHeartbeats 4000000 in
theorem evaluation_transform_exact (x : Fin 5 → ℝ) :
    T*(Polynomial.sylvester (modelP x) (modelQ x) 5 4) = pre x := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [Matrix.mul_apply,Fin.sum_univ_succ,T,pre,
    pre0,pre1,pre2,pre3,pre4,Polynomial.sylvester,Matrix.of_apply,
    Fin.addCases,Set.mem_Icc,modelP,modelQ,Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,pCoeffTable,qCoeffTable]
  all_goals ring

set_option maxHeartbeats 4000000 in
theorem column_transform_exact (x : Fin 5 → ℝ) : pre x*R = reduced x := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [Matrix.mul_apply,Fin.sum_univ_succ,pre,R,reduced,
    pre0,pre1,pre2,pre3,pre4,reduced0,reduced1,reduced2,reduced3,reduced4]
  all_goals ring

#print axioms T_inverse_exact
#print axioms R_inverse_exact
#print axioms evaluation_transform_exact
#print axioms column_transform_exact
end GProgram.G3.AllResidue.SliceThree
'''
(root/'program/G3SylvesterSliceThreeTransforms.lean').write_text(t)
print('transform generated',len(t))
