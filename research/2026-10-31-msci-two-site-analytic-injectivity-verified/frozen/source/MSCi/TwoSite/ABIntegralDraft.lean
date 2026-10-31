import MSCi.TwoSite.ABSurvivalDraft

/-!
Uncompiled candidate connection between the shifted AB formula and its
bounded survival integral with the common exponential root tail.

This is an analytic identity for the transcribed formula. It does not prove
that the declared survival curves are projections of the six-sample process,
that their crossing lies before the root, or full AB identifiability.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace MSCi.TwoSite

theorem ab_survival_integral_closed (T r z a : ℝ)
    (ha₀ : 0 ≤ a) (haT : a ≤ T) (hr : 0 < r) (hz : 0 < z) :
    (∫ t in (0 : ℝ)..T, Real.exp (-z * t) * abSurvival a r t) =
      (1 - Real.exp (-z * a)) / z +
        (Real.exp (-z * a) - Real.exp (-z * T) * Real.exp (-r * (T - a))) / (r + z) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hnz : -z ≠ 0 := neg_ne_zero.mpr hz0
  have hrz : r + z ≠ 0 := ne_of_gt (by positivity)
  have hnrz : -(r + z) ≠ 0 := neg_ne_zero.mpr hrz
  have hcont : Continuous (fun t : ℝ => Real.exp (-z * t) * abSurvival a r t) := by
    unfold abSurvival
    fun_prop
  have hI₁ := hcont.intervalIntegrable 0 a
  have hI₂ := hcont.intervalIntegrable a T
  have hearly : (∫ t in (0 : ℝ)..a, Real.exp (-z * t) * abSurvival a r t) =
      ∫ t in (0 : ℝ)..a, Real.exp (-z * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) a := by simpa [Set.uIcc_of_le ha₀] using ht
    rw [ab_survival_of_le a r t ht'.2]
    ring
  have hlate : (∫ t in a..T, Real.exp (-z * t) * abSurvival a r t) =
      ∫ t in a..T, Real.exp (r * a) * Real.exp (-(r + z) * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc a T := by simpa [Set.uIcc_of_le haT] using ht
    rw [ab_survival_of_ge a r t ht'.1, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hearly' : (∫ t in (0 : ℝ)..a, Real.exp (-z * t) * abSurvival a r t) =
      (1 - Real.exp (-z * a)) / z := by
    rw [hearly, integral_exp_linear (-z) 0 a hnz]
    simp only [mul_zero, Real.exp_zero]
    field_simp [hz0] <;> ring
  have hA : Real.exp (r * a) * Real.exp (-(r + z) * a) = Real.exp (-z * a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hT : Real.exp (r * a) * Real.exp (-(r + z) * T) =
      Real.exp (-z * T) * Real.exp (-r * (T - a)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hlate' : (∫ t in a..T, Real.exp (-z * t) * abSurvival a r t) =
      (Real.exp (-z * a) - Real.exp (-z * T) * Real.exp (-r * (T - a))) / (r + z) := by
    rw [hlate, intervalIntegral.integral_const_mul, integral_exp_linear (-(r + z)) a T hnrz]
    calc
      Real.exp (r * a) *
          ((Real.exp (-(r + z) * T) - Real.exp (-(r + z) * a)) / (-(r + z))) =
          (Real.exp (r * a) * Real.exp (-(r + z) * a) -
            Real.exp (r * a) * Real.exp (-(r + z) * T)) / (r + z) := by
        field_simp [hrz] <;> ring
      _ = _ := by rw [hA, hT]
  calc
    (∫ t in (0 : ℝ)..T, Real.exp (-z * t) * abSurvival a r t) =
        (∫ t in (0 : ℝ)..a, Real.exp (-z * t) * abSurvival a r t) +
          (∫ t in a..T, Real.exp (-z * t) * abSurvival a r t) := by
      exact (intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂).symm
    _ = _ := by rw [hearly', hlate']

/-- Bounded version of the Laplace/survival identity, including the root tail. -/
theorem ab_shifted_eq_survival_integral (T R r z a : ℝ)
    (ha₀ : 0 ≤ a) (haT : a ≤ T) (hR : 0 < R) (hr : 0 < r) (hz : 0 < z) :
    pulseShiftedMoment T R r z a = 1 - z *
      ((∫ t in (0 : ℝ)..T, Real.exp (-z * t) * abSurvival a r t) +
        Real.exp (-z * T) * abSurvival a r T / (R + z)) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hrz : r + z ≠ 0 := ne_of_gt (by positivity)
  have hRz : R + z ≠ 0 := ne_of_gt (by positivity)
  have he : Real.exp (-z * a) * Real.exp (-(r + z) * (T - a)) =
      Real.exp (-z * T) * Real.exp (-r * (T - a)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hM : pulseShiftedMoment T R r z a =
      r / (r + z) * (Real.exp (-z * a) - Real.exp (-z * T) * Real.exp (-r * (T - a))) +
        Real.exp (-z * T) * Real.exp (-r * (T - a)) * (R / (R + z)) := by
    unfold pulseShiftedMoment rootMoment
    calc
      _ = r / (r + z) * (Real.exp (-z * a) -
            Real.exp (-z * a) * Real.exp (-(r + z) * (T - a))) +
          Real.exp (-z * T) * Real.exp (-r * (T - a)) * (R / (R + z)) := by ring
      _ = _ := by rw [he]
  rw [hM, ab_survival_integral_closed T r z a ha₀ haT hr hz, ab_survival_of_ge a r T haT]
  field_simp [hz0, hrz, hRz] <;> ring

/-- Equal shifted moments imply the first weighted survival difference is zero. -/
theorem ab_equal_shifted_moment_implies_zero_weight (T R r₁ r₂ z a₁ a₂ : ℝ)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (h₁T : a₁ ≤ T) (h₂T : a₂ ≤ T)
    (hR : 0 < R) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hz : 0 < z)
    (heq : pulseShiftedMoment T R r₁ z a₁ = pulseShiftedMoment T R r₂ z a₂) :
    (∫ t in (0 : ℝ)..T, Real.exp (-z * t) * abSurvivalDiff a₁ r₁ a₂ r₂ t) +
      Real.exp (-z * T) * abSurvivalDiff a₁ r₁ a₂ r₂ T / (R + z) = 0 := by
  have hcont₁ : Continuous (fun t : ℝ => Real.exp (-z * t) * abSurvival a₁ r₁ t) := by
    unfold abSurvival
    fun_prop
  have hcont₂ : Continuous (fun t : ℝ => Real.exp (-z * t) * abSurvival a₂ r₂ t) := by
    unfold abSurvival
    fun_prop
  have hIdiff : (∫ t in (0 : ℝ)..T, Real.exp (-z * t) * abSurvivalDiff a₁ r₁ a₂ r₂ t) =
      (∫ t in (0 : ℝ)..T, Real.exp (-z * t) * abSurvival a₁ r₁ t) -
        (∫ t in (0 : ℝ)..T, Real.exp (-z * t) * abSurvival a₂ r₂ t) := by
    calc
      (∫ t in (0 : ℝ)..T, Real.exp (-z * t) * abSurvivalDiff a₁ r₁ a₂ r₂ t) =
          ∫ t in (0 : ℝ)..T, (Real.exp (-z * t) * abSurvival a₁ r₁ t -
            Real.exp (-z * t) * abSurvival a₂ r₂ t) := by
        apply intervalIntegral.integral_congr
        intro t _
        unfold abSurvivalDiff
        ring
      _ = _ := intervalIntegral.integral_sub (hcont₁.intervalIntegrable 0 T) (hcont₂.intervalIntegrable 0 T)
  rw [ab_shifted_eq_survival_integral T R r₁ z a₁ ha₁ h₁T hR hr₁ hz,
    ab_shifted_eq_survival_integral T R r₂ z a₂ ha₂ h₂T hR hr₂ hz] at heq
  rw [hIdiff]
  unfold abSurvivalDiff
  have hprod : -z *
      ((∫ t in (0 : ℝ)..T, Real.exp (-z * t) * abSurvival a₁ r₁ t) -
        (∫ t in (0 : ℝ)..T, Real.exp (-z * t) * abSurvival a₂ r₂ t) +
        Real.exp (-z * T) * (abSurvival a₁ r₁ T - abSurvival a₂ r₂ T) / (R + z)) = 0 := by
    nlinarith [heq]
  exact (mul_eq_zero.mp hprod).resolve_left (neg_ne_zero.mpr (ne_of_gt hz))

end MSCi.TwoSite
