import ResearchCommons.MSCI.KilledClocks
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact two-holding integration and finite exponential-sum closure.
UNCOMPILED, dot (OpenAI), 31 October 2026. Classical calculus, not a novelty
claim or assumed scientific likelihood expansion. Actual source specialization
uses its proved strict comparable-merger rates; no unrelated spectral divisor. -/
noncomputable section
set_option autoImplicit false
namespace ResearchCommons.MSCI.JC69HoldingConvolution
open MeasureTheory Real
open scoped BigOperators Interval

lemma exp_scaled_interval (c T : ℝ) (hc : c ≠ 0) :
    (∫ u in (0:ℝ)..T, Real.exp (c*u)) = (Real.exp (c*T)-1)/c := by
  have hd (x : ℝ) : HasDerivAt (fun u : ℝ => Real.exp (c*u)/c) (Real.exp (c*x)) x := by
    convert (((Real.hasDerivAt_exp (c*x)).comp x ((hasDerivAt_id x).const_mul c)).div_const c) using 1 <;>
      field_simp [hc] <;> ring
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (c*u)) volume 0 T :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (c*u))).intervalIntegrable 0 T
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hint]
  simp only [mul_zero,Real.exp_zero]
  ring

/-- Exact convolution including the terminal holding interval; valid even at
T=0. The only denominator is the actual earlier-minus-later rate. -/
theorem two_holding_convolution (a b T : ℝ) (hab : b < a) :
    (∫ u in (0:ℝ)..T, Real.exp (-a*u) * Real.exp (-b*(T-u))) =
      (Real.exp (-b*T)-Real.exp (-a*T))/(a-b) := by
  have hba : b-a ≠ 0 := sub_ne_zero.mpr (ne_of_lt hab)
  have hab' : a-b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hf (u : ℝ) : Real.exp (-a*u)*Real.exp (-b*(T-u)) =
      Real.exp (-b*T)*Real.exp ((b-a)*u) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  simp_rw [hf]
  rw [intervalIntegral.integral_const_mul,exp_scaled_interval _ _ hba]
  have hm : Real.exp (-b*T)*Real.exp ((b-a)*T) = Real.exp (-a*T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-a*T)-Real.exp (-b*T))/(b-a) := by
      rw [← mul_div_assoc,mul_sub,hm,mul_one]
    _ = _ := by field_simp [hba, hab']; ring

/-- One integration of a finite lower-state exponential sum adds at most ONE
new exponential base. Polynomial/rational coefficient construction and the
actual source-path expansion remain separate; no final expansion is assumed. -/
theorem convolve_finite_exponential_sum {I : Type*} [Fintype I]
    (a T : ℝ) (b coefficient : I → ℝ) (hab : ∀ i, b i < a) :
    (∫ u in (0:ℝ)..T, Real.exp (-a*u) *
      ∑ i, coefficient i * Real.exp (-b i*(T-u))) =
      (∑ i, (coefficient i/(a-b i)) * Real.exp (-b i*T)) -
        (∑ i, coefficient i/(a-b i)) * Real.exp (-a*T) := by
  have hf (u : ℝ) : Real.exp (-a*u) * (∑ i, coefficient i*Real.exp (-b i*(T-u))) =
      ∑ i, coefficient i * (Real.exp (-a*u)*Real.exp (-b i*(T-u))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [hf]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul,two_holding_convolution a _ T (hab _)]
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · intro i _
    exact (by fun_prop : Continuous (fun u : ℝ =>
      coefficient i*(Real.exp (-a*u)*Real.exp (-b i*(T-u))))).intervalIntegrable 0 T

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
variable {V E Copy X Site G : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [Fintype Site] [AddCommMonoid G] [DecidableEq G]

/-- Genuine original ordered-winner holding factor. No source transition law
is replaced: this evaluates the two exponential factors at the ACTUAL killed
rates and actual half pair-rate of that source choice. -/
theorem actual_one_merger_holding_integral (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (mu : ℝ) (hmu : 0 ≤ mu)
    (characters : Copy → Site → G) (s : Code N sample) (p : Choice N s) (T : ℝ) :
    (∫ u in (0:ℝ)..T, choiceRate N r s p *
      (Real.exp (-killedRate N r mu characters s*u) *
       Real.exp (-killedRate N r mu characters (stepDestination N s (some p))*(T-u)))) =
      choiceRate N r s p *
        ((Real.exp (-killedRate N r mu characters (stepDestination N s (some p))*T) -
          Real.exp (-killedRate N r mu characters s*T)) /
         (killedRate N r mu characters s -
          killedRate N r mu characters (stepDestination N s (some p)))) := by
  rw [intervalIntegral.integral_const_mul]
  rw [two_holding_convolution _ _ _ (actual_killedRate_strict_merger N r mu hmu characters s p)]

#print axioms two_holding_convolution
#print axioms convolve_finite_exponential_sum
#print axioms actual_one_merger_holding_integral
end ResearchCommons.MSCI.JC69HoldingConvolution
