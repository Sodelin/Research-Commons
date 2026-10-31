import MSCi.TwoSite.ABIntegralDraft

/-!
Uncompiled candidate ordering steps for the AB single-crossing proof.

For an earlier onset, equality of a first weighted survival integral rules
out an equal or faster early rate. With the resulting rate ordering, it also
forces the unique crossing to occur before the common root. These statements
still concern the declared analytic curves, not the six-sample source law.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace MSCi.TwoSite

theorem ab_nonpositive_weighted_difference_neg (D : ℝ → ℝ) (T R c x : ℝ)
    (hD : Continuous D) (hT : 0 < T) (hR : 0 < R) (hc : 0 < c)
    (hx₀ : 0 ≤ x) (hxT : x ≤ T) (hx : D x < 0)
    (hDnonpos : ∀ t ∈ Set.Icc (0 : ℝ) T, D t ≤ 0) (hend : D T ≤ 0) :
    (∫ t in (0 : ℝ)..T, Real.exp (-c * t) * D t) +
      Real.exp (-c * T) * D T / (R + c) < 0 := by
  have hcont : Continuous (fun t : ℝ => Real.exp (-c * t) * D t) := by fun_prop
  have hIneg : (∫ t in (0 : ℝ)..T, Real.exp (-c * t) * D t) < 0 := by
    have hpos : 0 < ∫ t in (0 : ℝ)..T, -(Real.exp (-c * t) * D t) := by
      apply intervalIntegral.integral_pos hT hcont.neg.continuousOn
      · intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
        exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
          (le_of_lt (Real.exp_pos _)) (hDnonpos t ht'))
      · exact ⟨x, ⟨hx₀, hxT⟩, neg_pos.mpr (mul_neg_of_pos_of_neg (Real.exp_pos _) hx)⟩
    rw [intervalIntegral.integral_neg] at hpos
    linarith
  have htail : Real.exp (-c * T) * D T / (R + c) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hend
    · positivity
  exact add_neg_of_neg_of_nonpos hIneg htail

theorem ab_earlier_faster_survival_diff_nonpos (a₁ r₁ a₂ r₂ t : ℝ)
    (ha : a₁ ≤ a₂) (hr₂ : 0 < r₂) (hrr : r₂ ≤ r₁) :
    abSurvivalDiff a₁ r₁ a₂ r₂ t ≤ 0 := by
  have hbase : t - a₂ ≤ t - a₁ := by linarith
  have hmax : max (t - a₂) 0 ≤ max (t - a₁) 0 := by
    exact max_le (le_trans hbase (le_max_left _ _)) (le_max_right _ _)
  have hmax0 : 0 ≤ max (t - a₁) 0 := le_max_right _ _
  have hprod₁ := mul_le_mul_of_nonneg_left hmax (le_of_lt hr₂)
  have hprod₂ := mul_le_mul_of_nonneg_right hrr hmax0
  have harg : -r₁ * max (t - a₁) 0 ≤ -r₂ * max (t - a₂) 0 := by nlinarith
  unfold abSurvivalDiff abSurvival
  exact sub_nonpos.mpr (Real.exp_le_exp.mpr harg)

/-- Equal first weighted moments force the earlier onset to use the lower rate. -/
theorem ab_earlier_rate_lt_of_zero_weight (a₁ r₁ a₂ r₂ T R c : ℝ)
    (ha₀ : 0 ≤ a₁) (ha : a₁ < a₂) (ha₂T : a₂ < T)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : 0 < R) (hc : 0 < c)
    (hzero : (∫ t in (0 : ℝ)..T, Real.exp (-c * t) * abSurvivalDiff a₁ r₁ a₂ r₂ t) +
        Real.exp (-c * T) * abSurvivalDiff a₁ r₁ a₂ r₂ T / (R + c) = 0) : r₁ < r₂ := by
  by_contra hnot
  have hrr : r₂ ≤ r₁ := le_of_not_gt hnot
  let x := (a₁ + a₂) / 2
  have hx₁ : a₁ < x := by dsimp [x]; linarith
  have hx₂ : x < a₂ := by dsimp [x]; linarith
  have hx₀ : 0 ≤ x := le_trans ha₀ (le_of_lt hx₁)
  have hxT : x ≤ T := le_of_lt (lt_trans hx₂ ha₂T)
  have hT : 0 < T := lt_of_le_of_lt ha₀ (lt_trans ha ha₂T)
  have hx : abSurvivalDiff a₁ r₁ a₂ r₂ x < 0 :=
    ab_survival_diff_neg_between_onsets a₁ r₁ a₂ r₂ x hr₁ hx₁ (le_of_lt hx₂)
  have hnonpos : ∀ t ∈ Set.Icc (0 : ℝ) T, abSurvivalDiff a₁ r₁ a₂ r₂ t ≤ 0 := by
    intro t _
    exact ab_earlier_faster_survival_diff_nonpos a₁ r₁ a₂ r₂ t (le_of_lt ha) hr₂ hrr
  have hend := ab_earlier_faster_survival_diff_nonpos a₁ r₁ a₂ r₂ T (le_of_lt ha) hr₂ hrr
  have hneg := ab_nonpositive_weighted_difference_neg (abSurvivalDiff a₁ r₁ a₂ r₂) T R c x
    (ab_survival_diff_continuous a₁ r₁ a₂ r₂) hT hR hc hx₀ hxT hx hnonpos hend
  linarith

theorem ab_survival_diff_zero_at_crossing (a₁ r₁ a₂ r₂ : ℝ)
    (ha : a₁ < a₂) (hr₁ : 0 < r₁) (hrr : r₁ < r₂) :
    abSurvivalDiff a₁ r₁ a₂ r₂ (abCrossing a₁ r₁ a₂ r₂) = 0 := by
  have hcross := ab_crossing_after_second_onset a₁ r₁ a₂ r₂ ha hr₁ hrr
  unfold abSurvivalDiff
  rw [ab_survival_of_ge a₁ r₁ _ (le_of_lt (lt_trans ha hcross)),
    ab_survival_of_ge a₂ r₂ _ (le_of_lt hcross)]
  apply sub_eq_zero.mpr
  apply congrArg Real.exp
  have hlog := ab_log_survival_diff a₁ r₁ a₂ r₂ (abCrossing a₁ r₁ a₂ r₂) hrr
  simp only [sub_self, mul_zero] at hlog
  linarith

theorem ab_survival_diff_nonpos_at_or_before_crossing (a₁ r₁ a₂ r₂ t : ℝ)
    (ha : a₁ < a₂) (hr₁ : 0 < r₁) (hrr : r₁ < r₂)
    (ht : t ≤ abCrossing a₁ r₁ a₂ r₂) : abSurvivalDiff a₁ r₁ a₂ r₂ t ≤ 0 := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact ab_survival_diff_nonpos_before_crossing a₁ r₁ a₂ r₂ t ha hr₁ hrr hlt
  · subst t
    exact le_of_eq (ab_survival_diff_zero_at_crossing a₁ r₁ a₂ r₂ ha hr₁ hrr)

/-- The first weighted equality rules out a crossing at or beyond the root. -/
theorem ab_crossing_before_root_of_zero_weight (a₁ r₁ a₂ r₂ T R c : ℝ)
    (ha₀ : 0 ≤ a₁) (ha : a₁ < a₂) (ha₂T : a₂ < T)
    (hr₁ : 0 < r₁) (hrr : r₁ < r₂) (hR : 0 < R) (hc : 0 < c)
    (hzero : (∫ t in (0 : ℝ)..T, Real.exp (-c * t) * abSurvivalDiff a₁ r₁ a₂ r₂ t) +
        Real.exp (-c * T) * abSurvivalDiff a₁ r₁ a₂ r₂ T / (R + c) = 0) :
    abCrossing a₁ r₁ a₂ r₂ < T := by
  by_contra hnot
  have hTcross : T ≤ abCrossing a₁ r₁ a₂ r₂ := le_of_not_gt hnot
  let x := (a₁ + a₂) / 2
  have hx₁ : a₁ < x := by dsimp [x]; linarith
  have hx₂ : x < a₂ := by dsimp [x]; linarith
  have hx₀ : 0 ≤ x := le_trans ha₀ (le_of_lt hx₁)
  have hxT : x ≤ T := le_of_lt (lt_trans hx₂ ha₂T)
  have hT : 0 < T := lt_of_le_of_lt ha₀ (lt_trans ha ha₂T)
  have hx : abSurvivalDiff a₁ r₁ a₂ r₂ x < 0 :=
    ab_survival_diff_neg_between_onsets a₁ r₁ a₂ r₂ x hr₁ hx₁ (le_of_lt hx₂)
  have hnonpos : ∀ t ∈ Set.Icc (0 : ℝ) T, abSurvivalDiff a₁ r₁ a₂ r₂ t ≤ 0 := by
    intro t ht
    exact ab_survival_diff_nonpos_at_or_before_crossing a₁ r₁ a₂ r₂ t ha hr₁ hrr
      (le_trans ht.2 hTcross)
  have hend := ab_survival_diff_nonpos_at_or_before_crossing a₁ r₁ a₂ r₂ T ha hr₁ hrr hTcross
  have hneg := ab_nonpositive_weighted_difference_neg (abSurvivalDiff a₁ r₁ a₂ r₂) T R c x
    (ab_survival_diff_continuous a₁ r₁ a₂ r₂) hT hR hc hx₀ hxT hx hnonpos hend
  linarith

end MSCi.TwoSite
