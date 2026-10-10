import UnifiedLean.Source.SourceDestinationClockReset
import UnifiedLean.Source.SourceEpochSemigroup
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Actual source epoch renewal identity for the timed-clock path binding

Contributor: dot, 2026-10-02. The generator row is DERIVED from the actual
source PMF. The exponential's first-jump integral equation is then derived by
the fundamental theorem of calculus, matching the literal winning-clock law
and actual merged-state reset already proved. A timed path/kernel equality
must still be assembled; an integral/source-law identity is not an input.
-/
namespace UnifiedLean.Source.SourceEpochRenewal
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix NormedSpace
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Actual generator row action, retaining every CURRENT original pair and
its actual merged destination. No fitted/desired generator row is assumed. -/
theorem actual_generator_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample)
    (F : Matrix (Code N sample) (Code N sample) ℝ) :
    (sourceGeneratorMatrix N (sample := sample) r * F) s d =
      (∑ p : Choice N s, choiceRate N r s p * F (stepDestination N s (some p)) d) -
        totalRate N r s * F s d := by
  unfold sourceGeneratorMatrix
  rw [Matrix.smul_mul,Matrix.sub_mul,Matrix.one_mul]
  change globalRateBound (Copy := Copy) r *
    ((∑ z : Code N sample, (sourceStep N r s z).toReal * F z d) - F s d) = _
  rw [sourceStep_expectation N r s (fun z => F z d),Fintype.sum_option]
  simp only [choiceMass,stepDestination]
  have hne := (globalRateBound_positive (Copy := Copy) r).ne'
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  field_simp [hne]
  ring

lemma actual_exponential_entry_derivative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => (exp ((t-v) • sourceGeneratorMatrix N (sample := sample) r)) s d)
      (-(sourceGeneratorMatrix N (sample := sample) r *
        exp ((t-u) • sourceGeneratorMatrix N (sample := sample) r)) s d) u := by
  let eval : Matrix (Code N sample) (Code N sample) ℝ →L[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ s d).toContinuousLinearMap
  have hm := (hasDerivAt_exp_smul_const' (sourceGeneratorMatrix N (sample := sample) r) (t-u)).scomp u
    ((hasDerivAt_const u t).sub (hasDerivAt_id u))
  have hh := eval.hasFDerivAt.comp_hasDerivAt u hm
  simpa only [eval,Function.comp_def,sub_self,zero_sub,neg_one_smul,ContinuousLinearMap.map_neg,
    LinearMap.coe_toContinuousLinearMap',Matrix.entryLinearMap_apply] using hh

lemma actual_renewal_derivative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-(totalRate N r s*v)) *
      (exp ((t-v) • sourceGeneratorMatrix N (sample := sample) r)) s d)
      (-(Real.exp (-(totalRate N r s*u)) *
        ∑ p : Choice N s, choiceRate N r s p *
          (exp ((t-u) • sourceGeneratorMatrix N (sample := sample) r))
            (stepDestination N s (some p)) d)) u := by
  have hE := actual_exponential_entry_derivative N r s d t u
  change HasDerivAt (fun v : ℝ => (exp ((t-v) • sourceGeneratorMatrix N (sample := sample) r)) s d)
    (-((sourceGeneratorMatrix N (sample := sample) r * exp ((t-u) • sourceGeneratorMatrix N (sample := sample) r)) s d)) u at hE
  rw [actual_generator_row] at hE
  have he := ((hasDerivAt_id u).const_mul (-totalRate N r s)).exp
  simp only [mul_one,neg_mul,id_eq] at he
  have hh := he.mul hE
  convert hh using 1 <;> first | rfl | ring

/-- First-jump renewal is a CONSEQUENCE of the actual generator and matrix
exponential. Its density uses actual original pair rates and actual merged
destinations, exactly as the literal clock/reset law does. -/
theorem actual_source_exponential_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t : ℝ) :
    (exp (t • sourceGeneratorMatrix N (sample := sample) r)) s d =
      Real.exp (-(totalRate N r s*t)) * (if s = d then 1 else 0) +
      ∫ u in 0..t, Real.exp (-(totalRate N r s*u)) *
        ∑ p : Choice N s, choiceRate N r s p *
          (exp ((t-u) • sourceGeneratorMatrix N (sample := sample) r))
            (stepDestination N s (some p)) d := by
  have hc : Continuous (fun u : ℝ => Real.exp (-(totalRate N r s*u)) *
      ∑ p : Choice N s, choiceRate N r s p *
        (exp ((t-u) • sourceGeneratorMatrix N (sample := sample) r))
          (stepDestination N s (some p)) d) := by
    apply Continuous.mul (by fun_prop)
    apply continuous_finsetSum
    intro p _
    exact continuous_const.mul (continuous_iff_continuousAt.mpr
      (fun u => (actual_exponential_entry_derivative N r (stepDestination N s (some p)) d t u).continuousAt))
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => actual_renewal_derivative N r s d t u) (hc.neg.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_neg] at hh
  simp only [sub_self,zero_smul,exp_zero,Matrix.one_apply,mul_zero,neg_zero,
    Real.exp_zero,one_mul,sub_zero] at hh
  linarith

/-- The actual constructed PMF satisfies the same first-jump recursion with
its actual future source kernels, not just a conditional matrix identity.
On the integration interval the remaining duration is EXACTLY t-u. -/
theorem actual_source_kernel_first_jump (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t : ℝ≥0) :
    (sourceTimeKernel N r t s d).toReal =
      Real.exp (-(totalRate N r s*(t : ℝ))) * (if s = d then 1 else 0) +
      ∫ u in 0..(t : ℝ), Real.exp (-(totalRate N r s*u)) *
        ∑ p : Choice N s, choiceRate N r s p *
          (sourceTimeKernel N r (Real.toNNReal ((t : ℝ)-u))
            (stepDestination N s (some p)) d).toReal := by
  rw [source_time_kernel_eq_exponential,actual_source_exponential_renewal]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  have hut : u ≤ (t : ℝ) := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hu
    exact hu.2
  simp_rw [source_time_kernel_eq_exponential,Real.coe_toNNReal _ (sub_nonneg.mpr hut)]

#print axioms actual_generator_row
#print axioms actual_exponential_entry_derivative
#print axioms actual_source_exponential_renewal
#print axioms actual_source_kernel_first_jump
end UnifiedLean.Source.SourceEpochRenewal
