import G3BernoulliVerticalExclusion
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Fixed-degree source-polynomial and specialization interfaces.
No exported resultant equality or nonzero-slice conclusion is assumed. -/
noncomputable section
namespace GProgram.G3.AllResidue
open scoped BigOperators
open Polynomial

def fullWeight (x : Fin 5 → ℝ) (i : Fin 6) : ℝ := match i.val with
  | 0 => x 0 | 1 => x 1 | 2 => x 2 | 3 => x 3 | 4 => x 4
  | _ => -(x 0+3*x 1+6*x 2+10*x 3+15*x 4)/21

def normalFreeWeight (r : ℝ) (i : Fin 5) : ℝ := match i.val with
  | 0 => normalB0 r | 1 => normalB1 r | 2 => normalB2 r
  | 3 => normalB3 r | _ => normalB4 r

theorem full_weight_drift_zero (x : Fin 5 → ℝ) :
    ∑ i, fullWeight x i * (capSevenExponent i : ℝ) = 0 := by
  norm_num [Fin.sum_univ_succ,fullWeight,capSevenExponent]
  ring

theorem full_weight_normal (r : ℝ) :
    fullWeight (normalFreeWeight r) = normalWeight r := by
  funext i
  fin_cases i <;> simp [fullWeight,normalFreeWeight,normalWeight]
  nlinarith [normal_drift r]

def sourceQProbabilityPolynomial (c : Fin 6 → ℝ) (exponent : Fin 6 → ℕ)
    (q : ℝ) : Polynomial ℝ :=
  ∑ i, C (c i*(exponent i : ℝ)*q^(exponent i-1)) *
    ∏ j ∈ Finset.univ.erase i, probabilityPolynomial (exponent j) q

theorem source_q_probability_eval (c : Fin 6 → ℝ) (exponent : Fin 6 → ℕ)
    (p q : ℝ) :
    (sourceQProbabilityPolynomial c exponent q).eval p =
      qCriticalNumerator c exponent p q := by
  simp only [sourceQProbabilityPolynomial,qCriticalNumerator,
    Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,probability_polynomial_eval]

theorem fixed_sylvester_specialization
    (f g : Polynomial (Polynomial ℝ)) (r : ℝ) :
    Polynomial.sylvester (f.map (Polynomial.evalRingHom r))
      (g.map (Polynomial.evalRingHom r)) 5 4 =
      (Polynomial.evalRingHom r).mapMatrix (Polynomial.sylvester f g 5 4) := by
  exact Polynomial.sylvester_map_map f g 5 4 (Polynomial.evalRingHom r)

theorem fixed_resultant_specialization
    (f g : Polynomial (Polynomial ℝ)) (r : ℝ) :
    Polynomial.resultant (f.map (Polynomial.evalRingHom r))
      (g.map (Polynomial.evalRingHom r)) 5 4 =
      (Polynomial.resultant f g 5 4).eval r := by
  exact Polynomial.resultant_map_map f g 5 4 (Polynomial.evalRingHom r)

#print axioms full_weight_drift_zero
#print axioms full_weight_normal
#print axioms source_q_probability_eval
#print axioms fixed_sylvester_specialization
#print axioms fixed_resultant_specialization
end GProgram.G3.AllResidue
