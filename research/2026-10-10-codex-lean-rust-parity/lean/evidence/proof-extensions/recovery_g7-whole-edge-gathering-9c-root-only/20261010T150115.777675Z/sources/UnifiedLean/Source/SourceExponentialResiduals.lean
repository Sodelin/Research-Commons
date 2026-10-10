import UnifiedLean.Source.SourceExponentialRaceDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Actual exponential residual clocks

Contributor: dot, 2026-10-02. This is the measure-level memorylessness used
inside the forthcoming winner-conditioned reset calculation. The law is
proved for the literal exponential measure, not supplied as a source field.
The connected next endpoint must retain the winner/time and all surviving
clock coordinates; deterministic survival alone is not a complete path law.
-/
namespace UnifiedLean.Source.SourceExponentialResiduals
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators NNReal ENNReal

lemma exponential_real_Iic {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (expMeasure r).real (Iic x) = if 0 ≤ x then 1-Real.exp (-(r*x)) else 0 := by
  letI := isProbabilityMeasure_expMeasure hr
  rw [← cdf_eq_real, cdf_expMeasure_eq hr]

lemma exponential_real_Ioc {r u x : ℝ} (hr : 0 < r) (hu : 0 ≤ u) (hx : 0 ≤ x) :
    (expMeasure r).real (Ioc u (u+x)) =
      Real.exp (-(r*u)) * (1-Real.exp (-(r*x))) := by
  letI := isProbabilityMeasure_expMeasure hr
  rw [← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.mpr (by linarith)) measurableSet_Iic,
    exponential_real_Iic hr, exponential_real_Iic hr, if_pos (by linarith : 0 ≤ u+x), if_pos hu]
  have hh : Real.exp (-(r*(u+x))) = Real.exp (-(r*u))*Real.exp (-(r*x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hh]
  ring

/-- Shift the actual surviving exponential clock by elapsed time. This exact
unnormalized measure identity retains the survival mass explicitly. -/
theorem actual_exponential_residual_measure {r : ℝ} (hr : 0 < r) (u : ℝ≥0) :
    ((expMeasure r).restrict (Ioi (u : ℝ))).map (fun y : ℝ => y-(u : ℝ)) =
      ENNReal.ofReal (Real.exp (-(r*(u : ℝ)))) • expMeasure r := by
  letI := isProbabilityMeasure_expMeasure hr
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage (by fun_prop : Measurable (fun y : ℝ => y-(u : ℝ))))]
  have hp : (fun y : ℝ => y-(u : ℝ)) ⁻¹' Iic x ∩ Ioi (u : ℝ) = Ioc (u : ℝ) ((u : ℝ)+x) := by
    ext y
    simp only [mem_inter_iff,mem_preimage,mem_Iic,mem_Ioi,mem_Ioc]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [hp]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).mp
  change (expMeasure r).real (Ioc (u : ℝ) ((u : ℝ)+x)) = _
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  change _ = Real.exp (-(r*(u : ℝ))) * (expMeasure r).real (Iic x)
  rw [exponential_real_Iic hr]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    exact exponential_real_Ioc hr (show (0 : ℝ) ≤ (u : ℝ) from u.property) hx
  · rw [if_neg hx,Ioc_eq_empty_of_le (by linarith),measureReal_empty,mul_zero]

variable {I : Type*} [Fintype I]

/-- All genuine surviving coordinates retain their independent original
exponential law after elapsed time is subtracted. No posterior law is an
input; the unnormalized survival factor is explicitly derived. -/
theorem actual_exponential_product_residual_measure (rate : I → ℝ)
    (hr : ∀ i, 0 < rate i) (u : ℝ≥0) :
    ((Measure.pi (fun i => expMeasure (rate i))).restrict
      (Set.univ.pi (fun _ : I => Ioi (u : ℝ)))).map
      (fun c : I → ℝ => fun i => c i-(u : ℝ)) =
      ENNReal.ofReal (Real.exp (-((∑ i, rate i)*(u : ℝ)))) •
        Measure.pi (fun i => expMeasure (rate i)) := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  rw [Measure.restrict_pi_pi,Measure.pi_map_pi (f := fun _ : I => fun y : ℝ => y-(u : ℝ)) (fun i => by fun_prop)]
  simp_rw [actual_exponential_residual_measure (hr _)]
  letI : ∀ i : I, IsFiniteMeasure (ENNReal.ofReal (Real.exp (-(rate i*(u : ℝ)))) • expMeasure (rate i)) :=
    fun i => Measure.smul_finite _ ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro sets hsets
  rw [Measure.smul_apply,smul_eq_mul,Measure.pi_pi]
  simp_rw [Measure.smul_apply,smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib,Finset.sum_mul]

/-- Equivalent arbitrary measurable residual-event form, used at the actual
random first winning time by Fubini in the connected race/reset theorem. -/
theorem actual_survivor_residual_event (rate : I → ℝ)
    (hr : ∀ i, 0 < rate i) (u : ℝ≥0) (B : Set (I → ℝ)) (hB : MeasurableSet B) :
    (Measure.pi (fun i => expMeasure (rate i)))
      ((fun c : I → ℝ => fun i => c i-(u : ℝ)) ⁻¹' B ∩
        Set.univ.pi (fun _ : I => Ioi (u : ℝ))) =
      ENNReal.ofReal (Real.exp (-((∑ i, rate i)*(u : ℝ)))) *
        (Measure.pi (fun i => expMeasure (rate i))) B := by
  have hh := congrArg (fun mu : Measure (I → ℝ) => mu B)
    (actual_exponential_product_residual_measure rate hr u)
  rw [Measure.map_apply (by fun_prop) hB,
    Measure.restrict_apply (hB.preimage (by fun_prop)),Measure.smul_apply,smul_eq_mul] at hh
  exact hh

#print axioms actual_exponential_residual_measure
#print axioms actual_exponential_product_residual_measure
#print axioms actual_survivor_residual_event
end UnifiedLean.Source.SourceExponentialResiduals
