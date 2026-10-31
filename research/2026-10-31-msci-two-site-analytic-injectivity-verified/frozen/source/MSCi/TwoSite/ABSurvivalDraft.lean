import MSCi.TwoSite.ABCrossingDraft

/-!
Uncompiled candidate survival-curve signs for the AB single-crossing proof.

The curves here describe survival only up to the common root time; the
bounded-crossing lemma separately accounts for the common exponential tail.
The crossing is still assumed to occur before the root, and the required
weighted integral has not yet been identified with the forward AB moment.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace MSCi.TwoSite

def abSurvival (a r t : ℝ) : ℝ := Real.exp (-r * max (t - a) 0)

def abSurvivalDiff (a₁ r₁ a₂ r₂ t : ℝ) : ℝ :=
  abSurvival a₁ r₁ t - abSurvival a₂ r₂ t

def abCrossing (a₁ r₁ a₂ r₂ : ℝ) : ℝ :=
  (r₂ * a₂ - r₁ * a₁) / (r₂ - r₁)

theorem ab_survival_of_le (a r t : ℝ) (h : t ≤ a) : abSurvival a r t = 1 := by
  unfold abSurvival
  rw [max_eq_right (sub_nonpos.mpr h)]
  simp

theorem ab_survival_of_ge (a r t : ℝ) (h : a ≤ t) :
    abSurvival a r t = Real.exp (-r * (t - a)) := by
  unfold abSurvival
  rw [max_eq_left (sub_nonneg.mpr h)]

theorem ab_survival_diff_continuous (a₁ r₁ a₂ r₂ : ℝ) :
    Continuous (abSurvivalDiff a₁ r₁ a₂ r₂) := by
  unfold abSurvivalDiff abSurvival
  fun_prop

theorem ab_crossing_after_second_onset (a₁ r₁ a₂ r₂ : ℝ)
    (ha : a₁ < a₂) (hr₁ : 0 < r₁) (hrr : r₁ < r₂) :
    a₂ < abCrossing a₁ r₁ a₂ r₂ := by
  have hden : 0 < r₂ - r₁ := sub_pos.mpr hrr
  unfold abCrossing
  apply (lt_div_iff₀ hden).2
  have hprod : 0 < r₁ * (a₂ - a₁) := mul_pos hr₁ (sub_pos.mpr ha)
  nlinarith

theorem ab_survival_diff_zero_before_first (a₁ r₁ a₂ r₂ t : ℝ)
    (ha : a₁ ≤ a₂) (ht : t ≤ a₁) : abSurvivalDiff a₁ r₁ a₂ r₂ t = 0 := by
  unfold abSurvivalDiff
  rw [ab_survival_of_le a₁ r₁ t ht, ab_survival_of_le a₂ r₂ t (le_trans ht ha)]
  ring

theorem ab_survival_diff_neg_between_onsets (a₁ r₁ a₂ r₂ t : ℝ)
    (hr₁ : 0 < r₁) (h₁ : a₁ < t) (h₂ : t ≤ a₂) :
    abSurvivalDiff a₁ r₁ a₂ r₂ t < 0 := by
  unfold abSurvivalDiff
  rw [ab_survival_of_ge a₁ r₁ t (le_of_lt h₁), ab_survival_of_le a₂ r₂ t h₂]
  apply sub_neg.mpr
  apply Real.exp_lt_one_iff.mpr
  have hprod : 0 < r₁ * (t - a₁) := mul_pos hr₁ (sub_pos.mpr h₁)
  nlinarith

theorem ab_log_survival_diff (a₁ r₁ a₂ r₂ t : ℝ) (hrr : r₁ < r₂) :
    (-r₁ * (t - a₁)) - (-r₂ * (t - a₂)) =
      (r₂ - r₁) * (t - abCrossing a₁ r₁ a₂ r₂) := by
  have hden : r₂ - r₁ ≠ 0 := ne_of_gt (sub_pos.mpr hrr)
  unfold abCrossing
  field_simp [hden] <;> ring

theorem ab_survival_diff_neg_after_second_before_crossing (a₁ r₁ a₂ r₂ t : ℝ)
    (hrr : r₁ < r₂) (ha : a₁ ≤ a₂) (ht : a₂ ≤ t)
    (hc : t < abCrossing a₁ r₁ a₂ r₂) : abSurvivalDiff a₁ r₁ a₂ r₂ t < 0 := by
  unfold abSurvivalDiff
  rw [ab_survival_of_ge a₁ r₁ t (le_trans ha ht), ab_survival_of_ge a₂ r₂ t ht]
  apply sub_neg.mpr
  apply Real.exp_lt_exp.mpr
  have hprod : (r₂ - r₁) * (t - abCrossing a₁ r₁ a₂ r₂) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hrr) (sub_neg.mpr hc)
  have hlog := ab_log_survival_diff a₁ r₁ a₂ r₂ t hrr
  linarith

theorem ab_survival_diff_pos_after_crossing (a₁ r₁ a₂ r₂ t : ℝ)
    (ha : a₁ < a₂) (hr₁ : 0 < r₁) (hrr : r₁ < r₂)
    (hc : abCrossing a₁ r₁ a₂ r₂ < t) : 0 < abSurvivalDiff a₁ r₁ a₂ r₂ t := by
  have hcross := ab_crossing_after_second_onset a₁ r₁ a₂ r₂ ha hr₁ hrr
  have ht : a₂ ≤ t := le_of_lt (lt_trans hcross hc)
  unfold abSurvivalDiff
  rw [ab_survival_of_ge a₁ r₁ t (le_trans (le_of_lt ha) ht), ab_survival_of_ge a₂ r₂ t ht]
  apply sub_pos.mpr
  apply Real.exp_lt_exp.mpr
  have hprod : 0 < (r₂ - r₁) * (t - abCrossing a₁ r₁ a₂ r₂) :=
    mul_pos (sub_pos.mpr hrr) (sub_pos.mpr hc)
  have hlog := ab_log_survival_diff a₁ r₁ a₂ r₂ t hrr
  linarith

theorem ab_survival_diff_nonpos_before_crossing (a₁ r₁ a₂ r₂ t : ℝ)
    (ha : a₁ < a₂) (hr₁ : 0 < r₁) (hrr : r₁ < r₂)
    (ht : t < abCrossing a₁ r₁ a₂ r₂) : abSurvivalDiff a₁ r₁ a₂ r₂ t ≤ 0 := by
  by_cases hfirst : t ≤ a₁
  · exact le_of_eq (ab_survival_diff_zero_before_first a₁ r₁ a₂ r₂ t (le_of_lt ha) hfirst)
  · have hfirst' : a₁ < t := lt_of_not_ge hfirst
    by_cases hsecond : t ≤ a₂
    · exact le_of_lt (ab_survival_diff_neg_between_onsets a₁ r₁ a₂ r₂ t hr₁ hfirst' hsecond)
    · have hsecond' : a₂ ≤ t := le_of_lt (lt_of_not_ge hsecond)
      exact le_of_lt (ab_survival_diff_neg_after_second_before_crossing
        a₁ r₁ a₂ r₂ t hrr (le_of_lt ha) hsecond' ht)

/-- Conditional composition: the ordered survival curves fit the crossing lemma. -/
theorem ab_ordered_crossing_separates (a₁ r₁ a₂ r₂ T R c : ℝ)
    (ha₀ : 0 ≤ a₁) (ha : a₁ < a₂) (hr₁ : 0 < r₁) (hrr : r₁ < r₂)
    (hR : 0 < R) (hc : 0 < c) (hsT : abCrossing a₁ r₁ a₂ r₂ < T)
    (hzero : (∫ t in (0 : ℝ)..T, Real.exp (-c * t) * abSurvivalDiff a₁ r₁ a₂ r₂ t) +
        Real.exp (-c * T) * abSurvivalDiff a₁ r₁ a₂ r₂ T / (R + c) = 0) :
    (∫ t in (0 : ℝ)..T, Real.exp (-(2 * c) * t) * abSurvivalDiff a₁ r₁ a₂ r₂ t) +
        Real.exp (-(2 * c) * T) * abSurvivalDiff a₁ r₁ a₂ r₂ T / (R + 2 * c) < 0 := by
  let s := abCrossing a₁ r₁ a₂ r₂
  let x := (a₁ + a₂) / 2
  have hcross : a₂ < s := ab_crossing_after_second_onset a₁ r₁ a₂ r₂ ha hr₁ hrr
  have hx₁ : a₁ < x := by dsimp [x]; linarith
  have hx₂ : x < a₂ := by dsimp [x]; linarith
  have hx0 : 0 ≤ x := le_trans ha₀ (le_of_lt hx₁)
  have hxs : x < s := lt_trans hx₂ hcross
  have hxT : x ≤ T := le_of_lt (lt_trans hxs hsT)
  have hs0 : 0 < s := lt_of_le_of_lt ha₀ (lt_trans ha hcross)
  have hxneg : abSurvivalDiff a₁ r₁ a₂ r₂ x < 0 :=
    ab_survival_diff_neg_between_onsets a₁ r₁ a₂ r₂ x hr₁ hx₁ (le_of_lt hx₂)
  have hleft : ∀ t ∈ Set.Icc (0 : ℝ) T, t < s → abSurvivalDiff a₁ r₁ a₂ r₂ t ≤ 0 := by
    intro t _ ht
    exact ab_survival_diff_nonpos_before_crossing a₁ r₁ a₂ r₂ t ha hr₁ hrr ht
  have hright : ∀ t ∈ Set.Icc (0 : ℝ) T, s < t → 0 ≤ abSurvivalDiff a₁ r₁ a₂ r₂ t := by
    intro t _ ht
    exact le_of_lt (ab_survival_diff_pos_after_crossing a₁ r₁ a₂ r₂ t ha hr₁ hrr ht)
  have hend : 0 ≤ abSurvivalDiff a₁ r₁ a₂ r₂ T :=
    le_of_lt (ab_survival_diff_pos_after_crossing a₁ r₁ a₂ r₂ T ha hr₁ hrr hsT)
  exact ab_bounded_crossing_separates (abSurvivalDiff a₁ r₁ a₂ r₂) T R c s x
    (ab_survival_diff_continuous a₁ r₁ a₂ r₂) hR hc hs0 hsT hx0 hxT hxs hxneg hleft hright hend hzero

end MSCi.TwoSite
