import MSCi.TwoSite.RootDraft

/-!
Uncompiled candidate pointwise ratio inequalities for the pulse step.

This does not establish the weighted-integral ratio, identify the pulse
parameters, or connect the formula map to the six-sample process. The
source and all proof terms await Lean checking and correspondence review.
-/

noncomputable section

namespace MSCi.TwoSite

/-- Pointwise score in the retained BC weighted-average argument. -/
def pulseScore (x B₁ B₂ : ℝ) : ℝ := (x ^ 2 - B₂) / (x - B₁)

theorem pulse_score_difference (a b B₁ B₂ : ℝ)
    (ha : a ≠ B₁) (hb : b ≠ B₁) :
    pulseScore b B₁ B₂ - pulseScore a B₁ B₂ =
      (b - a) * (1 + (B₂ - B₁ ^ 2) / ((b - B₁) * (a - B₁))) := by
  have ha' : a - B₁ ≠ 0 := sub_ne_zero.mpr ha
  have hb' : b - B₁ ≠ 0 := sub_ne_zero.mpr hb
  unfold pulseScore
  field_simp [ha', hb'] <;> ring

theorem pulse_score_strict_in_x (a b B₁ B₂ : ℝ)
    (ha : B₁ < a) (hab : a < b) (hvar : B₁ ^ 2 < B₂) :
    pulseScore a B₁ B₂ < pulseScore b B₁ B₂ := by
  have hb : B₁ < b := lt_trans ha hab
  have hd1 : 0 < b - B₁ := sub_pos.mpr hb
  have hd2 : 0 < a - B₁ := sub_pos.mpr ha
  have hf : 0 < (B₂ - B₁ ^ 2) / ((b - B₁) * (a - B₁)) :=
    div_pos (sub_pos.mpr hvar) (mul_pos hd1 hd2)
  have hp : 0 < (b - a) * (1 + (B₂ - B₁ ^ 2) / ((b - B₁) * (a - B₁))) :=
    mul_pos (sub_pos.mpr hab) (by linarith)
  rw [← pulse_score_difference a b B₁ B₂ (ne_of_gt ha) (ne_of_gt hb)] at hp
  exact sub_pos.mp hp

/-- Candidate strict variance gap for the positive-rate root transform. -/
theorem root_moment_variance_pos (T R c : ℝ) (hR : 0 < R) (hc : 0 < c) :
    rootMoment T R c ^ 2 < rootMoment T R (2 * c) := by
  have hm : 0 < rootMoment T R c := by
    unfold rootMoment
    positivity
  have hs : 0 < rootMoment T R c ^ 2 := by positivity
  have hratio : 1 < rootMoment T R (2 * c) / rootMoment T R c ^ 2 := by
    rw [rootMoments_ratio T R c hR hc]
    exact rootRatio_gt_one R c hR hc
  have h := (lt_div_iff₀ hs).mp hratio
  nlinarith

theorem root_moment_lt_exp_at (T R c t : ℝ) (hR : 0 < R) (hc : 0 < c)
    (ht : t ≤ T) : rootMoment T R c < Real.exp (-c * t) := by
  have hden : 0 < R + c := by positivity
  have hratio : R / (R + c) < 1 := (div_lt_one hden).2 (by linarith)
  have hbase : rootMoment T R c < Real.exp (-c * T) := by
    have h := mul_lt_mul_of_pos_left hratio (Real.exp_pos (-c * T))
    simpa [rootMoment] using h
  have hm : 0 ≤ c * (T - t) := mul_nonneg (le_of_lt hc) (sub_nonneg.mpr ht)
  have he : Real.exp (-c * T) ≤ Real.exp (-c * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact lt_of_lt_of_le hbase he

/-- The pointwise BC score strictly decreases as time increases up to T. -/
theorem pulse_score_strict_decrease_time (T R c t₁ t₂ : ℝ)
    (hR : 0 < R) (hc : 0 < c) (h12 : t₁ < t₂) (h2 : t₂ ≤ T) :
    pulseScore (Real.exp (-c * t₂)) (rootMoment T R c) (rootMoment T R (2 * c)) <
      pulseScore (Real.exp (-c * t₁)) (rootMoment T R c) (rootMoment T R (2 * c)) := by
  have ha := root_moment_lt_exp_at T R c t₂ hR hc h2
  have hd : 0 < c * (t₂ - t₁) := mul_pos hc (sub_pos.mpr h12)
  have hab : Real.exp (-c * t₂) < Real.exp (-c * t₁) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact pulse_score_strict_in_x _ _ _ _ ha hab (root_moment_variance_pos T R c hR hc)

/-- Algebraic combination of two strictly separated weighted segments. -/
theorem weighted_split_ratio_strict (wl wr il ir middle : ℝ)
    (hwl : 0 < wl) (hwr : 0 < wr)
    (hleft : middle * wl < il) (hright : ir < middle * wr) :
    ir / wr < (il + ir) / (wl + wr) := by
  have h1 : 0 < (il - middle * wl) * wr := mul_pos (sub_pos.mpr hleft) hwr
  have h2 : 0 < (middle * wr - ir) * wl := mul_pos (sub_pos.mpr hright) hwl
  have hnum : ir * (wl + wr) < (il + ir) * wr := by nlinarith
  exact (div_lt_div_iff₀ hwr (add_pos hwl hwr)).2 hnum

end MSCi.TwoSite
