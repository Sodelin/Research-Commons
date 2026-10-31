import MSCi.TwoSite.PulseIntegralDraft

/-!
Uncompiled candidate instantiation of the generic weighted-tail lemma with
the analytic BC score and weights. The equality of these integrals with the
declared BC forward moments, and their source-process derivation, remain
separate obligations. No Lean check has been performed.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace MSCi.TwoSite

def pulseWeight (T R r c t : ℝ) : ℝ :=
  Real.exp (-r * t) * (Real.exp (-c * t) - rootMoment T R c)

def pulseScoreAt (T R c t : ℝ) : ℝ :=
  pulseScore (Real.exp (-c * t)) (rootMoment T R c) (rootMoment T R (2 * c))

def pulseKernelTwo (T R r c t : ℝ) : ℝ :=
  Real.exp (-r * t) * (Real.exp (-(2 * c) * t) - rootMoment T R (2 * c))

theorem pulse_weight_positive (T R r c t : ℝ) (hR : 0 < R) (hc : 0 < c)
    (ht : t ≤ T) : 0 < pulseWeight T R r c t := by
  unfold pulseWeight
  exact mul_pos (Real.exp_pos _) (sub_pos.mpr (root_moment_lt_exp_at T R c t hR hc ht))

theorem pulse_weight_continuous (T R r c : ℝ) : Continuous (pulseWeight T R r c) := by
  unfold pulseWeight
  fun_prop

theorem pulse_score_continuousOn (T R c : ℝ) (hR : 0 < R) (hc : 0 < c) :
    ContinuousOn (pulseScoreAt T R c) (Set.Iic T) := by
  have hn : Continuous (fun t : ℝ =>
      Real.exp (-c * t) ^ 2 - rootMoment T R (2 * c)) := by fun_prop
  have hd : Continuous (fun t : ℝ =>
      Real.exp (-c * t) - rootMoment T R c) := by fun_prop
  have hz : ∀ t ∈ Set.Iic T, Real.exp (-c * t) - rootMoment T R c ≠ 0 := by
    intro t ht
    exact ne_of_gt (sub_pos.mpr (root_moment_lt_exp_at T R c t hR hc ht))
  simpa [pulseScoreAt, pulseScore] using hn.continuousOn.div hd.continuousOn hz

/-- The second weighted integrand is the declared second-moment kernel. -/
theorem pulse_weight_mul_score (T R r c t : ℝ) (hR : 0 < R) (hc : 0 < c)
    (ht : t ≤ T) : pulseWeight T R r c t * pulseScoreAt T R c t =
      pulseKernelTwo T R r c t := by
  have hne : Real.exp (-c * t) - rootMoment T R c ≠ 0 :=
    ne_of_gt (sub_pos.mpr (root_moment_lt_exp_at T R c t hR hc ht))
  have he2 : Real.exp (-(2 * c) * t) = Real.exp (-c * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold pulseWeight pulseScoreAt pulseScore pulseKernelTwo
  rw [he2]
  field_simp [hne] <;> ring

/-- Strict decrease of the two analytic kernel integrals' ratio. -/
theorem pulse_kernel_ratio_strict (T R r c a b : ℝ)
    (hR : 0 < R) (hc : 0 < c) (hab : a < b) (hbT : b < T) :
    (∫ t in b..T, pulseKernelTwo T R r c t) /
        (∫ t in b..T, pulseWeight T R r c t) <
      (∫ t in a..T, pulseKernelTwo T R r c t) /
        (∫ t in a..T, pulseWeight T R r c t) := by
  have hsub : Set.Icc a T ⊆ Set.Iic T := by
    intro t ht
    exact ht.2
  have hw := (pulse_weight_continuous T R r c).continuousOn
  have hq := (pulse_score_continuousOn T R c hR hc).mono hsub
  have hwpos : ∀ t ∈ Set.Icc a T, 0 < pulseWeight T R r c t := by
    intro t ht
    exact pulse_weight_positive T R r c t hR hc ht.2
  have hanti : StrictAntiOn (pulseScoreAt T R c) (Set.Icc a T) := by
    intro x hx y hy hxy
    exact pulse_score_strict_decrease_time T R c x y hR hc hxy hy.2
  have hresult := weighted_tail_ratio_strict
    (pulseWeight T R r c) (pulseScoreAt T R c) a b T hab hbT hw hq hwpos hanti
  have hnum (d : ℝ) (hd : d ≤ T) :
      (∫ t in d..T, pulseWeight T R r c t * pulseScoreAt T R c t) =
        (∫ t in d..T, pulseKernelTwo T R r c t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc d T := by simpa [Set.uIcc_of_le hd] using ht
    exact pulse_weight_mul_score T R r c t hR hc ht'.2
  rw [hnum b (le_of_lt hbT), hnum a (le_trans (le_of_lt hab) (le_of_lt hbT))] at hresult
  exact hresult

end MSCi.TwoSite
