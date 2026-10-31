import ResearchCommons.MSCI.JC69WeightedTrace
import ResearchCommons.MSCI.KilledClocks

/-! Actual original weighted renewal, with its exponential waiting measure
converted to Lebesgue density. UNCOMPILED, dot (OpenAI), 31 October 2026.
No final likelihood expansion, success normalization, root limit or replaced
process is assumed. Future actual finite-fuel failure flags are unchanged. -/
noncomputable section
set_option autoImplicit false
namespace ResearchCommons.MSCI.JC69ActualDensity
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators NNReal ENNReal

/-- Exact finite-density conversion, even for a nonmeasurable nonnegative
extended-real integrand. No cancellation of an infinite integrand is used. -/
lemma winner_density (C r T : ℝ) (hC : 0 < C) (hr : 0 ≤ r) (hT : 0 ≤ T)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ u, f u ∂((ENNReal.ofReal (r/C) • expMeasure C).restrict (Iic T))) =
      ∫⁻ u in Icc 0 T, ENNReal.ofReal (r * Real.exp (-(C*u))) * f u := by
  rw [Measure.restrict_smul,lintegral_smul_measure]
  simp only [smul_eq_mul]
  have hd : (∫⁻ u in Iic T, f u ∂expMeasure C) =
      ∫⁻ u in Iic T, exponentialPDF C u * f u := by
    change (∫⁻ u in Iic T, f u ∂volume.withDensity (exponentialPDF C)) = _
    exact setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
      (by unfold exponentialPDF; fun_prop) f measurableSet_Iic
      (Filter.Eventually.of_forall (fun _ => by unfold exponentialPDF; exact ENNReal.ofReal_lt_top))
  rw [hd,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ hT]
  have hz : (∫⁻ u in Iio (0:ℝ),
      ENNReal.ofReal (r/C) * (exponentialPDF C u * f u)) = 0 := by
    calc
      _ = ∫⁻ u in Iio (0:ℝ), (0:ℝ≥0∞) := by
        apply setLIntegral_congr_fun measurableSet_Iio
        intro u hu
        change ENNReal.ofReal (r/C) * (exponentialPDF C u * f u) = 0
        rw [exponentialPDF_of_neg hu]
        simp
      _ = 0 := by simp
  rw [hz,zero_add]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro u hu
  change ENNReal.ofReal (r/C) * (exponentialPDF C u * f u) =
    ENNReal.ofReal (r * Real.exp (-(C*u))) * f u
  rw [exponentialPDF_of_nonneg hu.1,← mul_assoc,
    ← ENNReal.ofReal_mul (div_nonneg hr hC.le)]
  congr 2
  field_simp [hC.ne']

open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69WeightedTrace
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Actual source Volterra identity. Each continuation is the SAME original
weighted trace law at actual destination and remaining horizon, with its
future failure flag and finite-fuel index n. C=0 is not divided by here: if an
actual choice p exists, its positive rate supplies C>0; otherwise the sum is
empty and the original no-event term remains. -/
theorem actual_weighted_density_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) :
    actualLocusWeight N r L q (n+1) s t =
      ENNReal.ofReal (Real.exp (-((totalRate N r s + locusKill N L q s)*(t:ℝ)))) +
      ∑ p : Choice N s, ∫⁻ u in Icc (0:ℝ) (t:ℝ),
        ENNReal.ofReal (choiceRate N r s p *
          Real.exp (-((totalRate N r s + locusKill N L q s)*u))) *
        actualLocusWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u) := by
  rw [actual_weighted_trace_renewal]
  apply congrArg₂ (· + ·)
  · rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
    congr 2
    ring
  · apply Finset.sum_congr rfl
    intro p _
    have hr := actual_choiceRate_positive N r s p
    have hC : 0 < totalRate N r s :=
      hr.trans_le (Finset.single_le_sum
        (fun i _ => (actual_choiceRate_positive N r s i).le) (Finset.mem_univ p))
    rw [winner_density (totalRate N r s) (choiceRate N r s p) (t:ℝ) hC hr.le t.property
      (fun u => ENNReal.ofReal (Real.exp (-(locusKill N L q s*u))) *
        actualLocusWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u))]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u _
    change ENNReal.ofReal (choiceRate N r s p * Real.exp (-(totalRate N r s*u))) *
      (ENNReal.ofReal (Real.exp (-(locusKill N L q s*u))) *
        actualLocusWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u)) =
      ENNReal.ofReal (choiceRate N r s p *
        Real.exp (-((totalRate N r s+locusKill N L q s)*u))) *
        actualLocusWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u)
    rw [← mul_assoc,← ENNReal.ofReal_mul
      (mul_nonneg hr.le (Real.exp_nonneg _))]
    congr 2
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring

#print axioms winner_density
#print axioms actual_weighted_density_renewal
end ResearchCommons.MSCI.JC69ActualDensity
