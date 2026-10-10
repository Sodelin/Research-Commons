import UnifiedLean.Source.SourcePoissonKernel
import UnifiedLean.Source.SourceGeneratorExponential

/-!
# Actual source Poisson kernel equals its generator exponential

Contributor: dot, 2026-10-02. This connects the two constructed finite-time
objects: the genuine PMF obtained from original source steps and Poisson counts,
and the original-generator matrix exponential. Positivity/normalization follow
from the PMF, rather than being assumed for the exponential. Calendar-compatible
initialization, the physical exponential-clock path law, timed observations and
unranked genealogy quotient remain the original temporal source assembly gate.
-/
namespace UnifiedLean.Source.SourcePoissonExponential
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source ProbabilityTheory MeasureTheory Matrix NormedSpace
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma bind_probability_real {A B : Type*} (p : PMF A) (f : A → PMF B) (b : B) :
    ((p.bind f) b).toReal = ∑' a, (p a).toReal * (f a b).toReal := by
  rw [PMF.bind_apply,ENNReal.tsum_toReal_eq (fun a =>
    ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (f a) b))]
  simp only [ENNReal.toReal_mul]

lemma source_iteration_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s d : Code N sample) :
    (sourceIteration N r k s d).toReal = (sourceTransition N r ^ k) s d := by
  induction k generalizing s with
  | zero =>
      simp only [sourceIteration,pow_zero,PMF.pure_apply,Matrix.one_apply]
      by_cases h : d = s
      · simp [h]
      · simp [h,Ne.symm h]
  | succ k ih =>
      rw [sourceIteration,bind_probability_real,tsum_fintype,pow_succ',Matrix.mul_apply]
      simp_rw [ih]
      rfl

lemma countPMF_real (rate : ℝ≥0) (k : Nat) :
    (countPMF rate k).toReal = Real.exp (-(rate : ℝ)) * (rate : ℝ)^k / k.factorial := by
  rw [countPMF,Measure.toPMF_apply,poissonMeasure_singleton,ENNReal.toReal_ofReal (by positivity)]

/-- Standard exponential-series identity instantiated later at the ACTUAL
source transition matrix. Neither stochasticity nor any desired source row
identity is a premise of this algebraic calculation. -/
lemma poisson_matrix_entry {I : Type*} [Fintype I] [DecidableEq I]
    (K : Matrix I I ℝ) (a : ℝ) (s d : I) :
    (∑' k : Nat, (Real.exp (-a) * a^k / k.factorial) * (K^k) s d) =
      (exp (a • (K-1))) s d := by
  let entry : Matrix I I ℝ →+ ℝ :=
    {toFun := fun M => M s d, map_zero' := rfl, map_add' := by intros; rfl}
  have he := (exp_series_hasSum_exp' (𝕂 := ℝ) (a • K)).map entry (by
    change Continuous (fun M : Matrix I I ℝ => M s d)
    fun_prop)
  change HasSum (fun k : Nat => (((k.factorial : ℝ)⁻¹) • (a • K)^k) s d)
    ((exp (a • K)) s d) at he
  have hh : HasSum (fun k : Nat => (Real.exp (-a) * a^k / k.factorial) * (K^k) s d)
      (Real.exp (-a) * (exp (a • K)) s d) := by
    simpa only [Function.comp_apply,entry,AddMonoidHom.coe_mk,smul_pow,
      Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
      using he.mul_left (Real.exp (-a))
  have hscalar : exp ((-a) • (1 : Matrix I I ℝ)) = Real.exp (-a) • (1 : Matrix I I ℝ) := by
    simpa only [Algebra.algebraMap_eq_smul_one,← Real.exp_eq_exp_ℝ] using
      (algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix I I ℝ) (-a)).symm
  have hcomm : Commute ((-a) • (1 : Matrix I I ℝ)) (a • K) :=
    (Commute.one_left K).smul_left (-a) |>.smul_right a
  have hsum : a • (K-1) = (-a) • (1 : Matrix I I ℝ) + a • K := by
    simp only [smul_sub,neg_smul]
    abel
  rw [hh.tsum_eq,hsum,exp_add_of_commute hcomm,hscalar,Matrix.smul_mul,Matrix.one_mul]
  rfl

/-- Equality of the GENUINE normalized original-source finite-time PMF and
its proved original-generator exponential, for every nonnegative duration. -/
theorem source_time_kernel_eq_exponential (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample) :
    (sourceTimeKernel N r t s d).toReal =
      (exp ((t : ℝ) • sourceGeneratorMatrix N (sample := sample) r)) s d := by
  rw [sourceTimeKernel,bind_probability_real]
  simp_rw [countPMF_real,source_iteration_probability]
  rw [poisson_matrix_entry]
  apply congrArg (fun M : Matrix (Code N sample) (Code N sample) ℝ => (exp M) s d)
  simp only [sourceGeneratorMatrix,smul_smul,NNReal.coe_mul]
  congr 1
  change globalRateBound (Copy := Copy) r * (t : ℝ) = (t : ℝ) * globalRateBound (Copy := Copy) r
  exact mul_comm _ _

#print axioms bind_probability_real
#print axioms source_iteration_probability
#print axioms poisson_matrix_entry
#print axioms source_time_kernel_eq_exponential
end UnifiedLean.Source.SourcePoissonExponential
