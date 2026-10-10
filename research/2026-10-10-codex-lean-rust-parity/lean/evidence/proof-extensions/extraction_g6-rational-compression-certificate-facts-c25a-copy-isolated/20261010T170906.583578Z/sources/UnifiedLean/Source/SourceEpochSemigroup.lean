import UnifiedLean.Source.SourcePoissonExponential

/-!
# Actual finite-source stochastic epoch semigroup

Contributor: dot, 2026-10-02. The constructed original-source PMF is a genuine
continuous-time transition semigroup on its fixed finite admitted carrier.
Identity and temporal composition are proved via its already-derived generator
exponential. Positivity/row normalization of that exponential are consequences
of the actual PMF. This is an epoch law; the finite original calendar agenda,
exponential holding-clock path binding and timed/unranked readout still require
source assembly, and no copied target equation is supplied as input.
-/
namespace UnifiedLean.Source.SourceEpochSemigroup
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source Matrix NormedSpace
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma pmf_sum_real {A : Type*} [Fintype A] (p : PMF A) : ∑ a : A, (p a).toReal = 1 := by
  have h : (∑ a : A, p a) = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)] at hr
  simpa only [ENNReal.toReal_one] using hr

/-- Normalization is inherited from a constructed probability distribution;
it is not assumed as a matrix or source contract field. -/
theorem actual_source_exponential_stochastic (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) :
    (∀ s d : Code N sample, 0 ≤ (exp ((t : ℝ) • sourceGeneratorMatrix N (sample := sample) r)) s d) ∧
      (∀ s : Code N sample, (∑ d : Code N sample,
        (exp ((t : ℝ) • sourceGeneratorMatrix N (sample := sample) r)) s d) = 1) := by
  constructor
  · intro s d
    rw [← source_time_kernel_eq_exponential]
    exact ENNReal.toReal_nonneg
  · intro s
    simp_rw [← source_time_kernel_eq_exponential]
    exact pmf_sum_real _

/-- The source kernel starts at the actual supplied admitted state. -/
theorem actual_source_time_zero (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : sourceTimeKernel N r 0 s = PMF.pure s := by
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [source_time_kernel_eq_exponential]
  simp only [NNReal.coe_zero,zero_smul,exp_zero,Matrix.one_apply,PMF.pure_apply]
  by_cases h : d = s
  · simp [h]
  · simp [h,Ne.symm h]

/-- Full admitted-state Chapman--Kolmogorov law of the ORIGINAL source
kernel, derived from its actual PMF/generator instance. -/
theorem actual_source_time_add (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t u : ℝ≥0) (s : Code N sample) :
    sourceTimeKernel N r (t+u) s =
      (sourceTimeKernel N r t s).bind (fun d => sourceTimeKernel N r u d) := by
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [bind_probability_real,tsum_fintype]
  simp_rw [source_time_kernel_eq_exponential]
  change (exp (((t+u : ℝ≥0) : ℝ) • sourceGeneratorMatrix N (sample := sample) r)) s d =
    (exp ((t : ℝ) • sourceGeneratorMatrix N (sample := sample) r) *
      exp ((u : ℝ) • sourceGeneratorMatrix N (sample := sample) r)) s d
  rw [NNReal.coe_add,add_smul,NormedSpace.exp_add_of_commute
    ((Commute.refl (sourceGeneratorMatrix N (sample := sample) r)).smul_left (t : ℝ)
      |>.smul_right (u : ℝ))]

#print axioms actual_source_exponential_stochastic
#print axioms actual_source_time_zero
#print axioms actual_source_time_add
end UnifiedLean.Source.SourceEpochSemigroup
