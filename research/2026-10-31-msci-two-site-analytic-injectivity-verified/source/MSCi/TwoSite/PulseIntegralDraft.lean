import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import MSCi.TwoSite.PulseScoreDraft

/-!
Uncompiled candidate strict weighted-tail average lemma.

The result below is a generic interval-integral statement for a continuous,
strictly decreasing score and a positive continuous weight. Its hypotheses
still need to be established for the actual BC formula, and the BC moment
ratio itself must be derived from the stochastic source. No Lean check has
been performed.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace MSCi.TwoSite

/-- Removing a nonempty initial interval lowers a strictly decreasing average. -/
theorem weighted_tail_ratio_strict (w q : ℝ → ℝ) (a b c : ℝ)
    (hab : a < b) (hbc : b < c)
    (hw : ContinuousOn w (Set.Icc a c))
    (hq : ContinuousOn q (Set.Icc a c))
    (hwpos : ∀ t ∈ Set.Icc a c, 0 < w t)
    (hanti : StrictAntiOn q (Set.Icc a c)) :
    (∫ t in b..c, w t * q t) / (∫ t in b..c, w t) <
      (∫ t in a..c, w t * q t) / (∫ t in a..c, w t) := by
  have hac : a ≤ c := le_trans (le_of_lt hab) (le_of_lt hbc)
  have ha : a ∈ Set.Icc a c := ⟨le_rfl, hac⟩
  have hb : b ∈ Set.Icc a c := ⟨le_of_lt hab, le_of_lt hbc⟩
  have hc : c ∈ Set.Icc a c := ⟨hac, le_rfl⟩
  have hsubL : Set.Icc a b ⊆ Set.Icc a c :=
    Set.Icc_subset_Icc le_rfl (le_of_lt hbc)
  have hsubR : Set.Icc b c ⊆ Set.Icc a c :=
    Set.Icc_subset_Icc (le_of_lt hab) le_rfl
  have hwL := hw.mono hsubL
  have hwR := hw.mono hsubR
  have hqL := hq.mono hsubL
  have hqR := hq.mono hsubR
  have hIwL : IntervalIntegrable w volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hab) hwL
  have hIwR : IntervalIntegrable w volume b c :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hbc) hwR
  have hIqL : IntervalIntegrable (fun t => w t * q t) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hab) (hwL.mul hqL)
  have hIqR : IntervalIntegrable (fun t => w t * q t) volume b c :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hbc) (hwR.mul hqR)
  have hwLpos : 0 < ∫ t in a..b, w t := by
    apply intervalIntegral.integral_pos hab hwL
    · intro t ht
      have ht' : t ∈ Set.Icc a c :=
        ⟨le_of_lt ht.1, le_trans ht.2 (le_of_lt hbc)⟩
      exact le_of_lt (hwpos t ht')
    · exact ⟨a, ⟨le_rfl, le_of_lt hab⟩, hwpos a ha⟩
  have hwRpos : 0 < ∫ t in b..c, w t := by
    apply intervalIntegral.integral_pos hbc hwR
    · intro t ht
      have ht' : t ∈ Set.Icc a c :=
        ⟨le_trans (le_of_lt hab) (le_of_lt ht.1), ht.2⟩
      exact le_of_lt (hwpos t ht')
    · exact ⟨b, ⟨le_rfl, le_of_lt hbc⟩, hwpos b hb⟩
  have hleft_pos : 0 < ∫ t in a..b, w t * (q t - q b) := by
    apply intervalIntegral.integral_pos hab (hwL.mul (hqL.sub continuousOn_const))
    · intro t ht
      have ht' : t ∈ Set.Icc a c :=
        ⟨le_of_lt ht.1, le_trans ht.2 (le_of_lt hbc)⟩
      have hqle : q b ≤ q t := by
        rcases lt_or_eq_of_le ht.2 with hlt | heq
        · exact le_of_lt (hanti ht' hb hlt)
        · subst t
          exact le_rfl
      exact mul_nonneg (le_of_lt (hwpos t ht')) (sub_nonneg.mpr hqle)
    · exact ⟨a, ⟨le_rfl, le_of_lt hab⟩,
        mul_pos (hwpos a ha) (sub_pos.mpr (hanti ha hb hab))⟩
  have hright_pos : 0 < ∫ t in b..c, w t * (q b - q t) := by
    apply intervalIntegral.integral_pos hbc (hwR.mul (continuousOn_const.sub hqR))
    · intro t ht
      have ht' : t ∈ Set.Icc a c :=
        ⟨le_trans (le_of_lt hab) (le_of_lt ht.1), ht.2⟩
      exact le_of_lt (mul_pos (hwpos t ht') (sub_pos.mpr (hanti hb ht' ht.1)))
    · exact ⟨c, ⟨le_of_lt hbc, le_rfl⟩,
        mul_pos (hwpos c hc) (sub_pos.mpr (hanti hb hc hbc))⟩
  simp_rw [mul_sub] at hleft_pos hright_pos
  rw [intervalIntegral.integral_sub hIqL (hIwL.mul_const (q b)),
    intervalIntegral.integral_mul_const] at hleft_pos
  rw [intervalIntegral.integral_sub (hIwR.mul_const (q b)) hIqR,
    intervalIntegral.integral_mul_const] at hright_pos
  have hleft : q b * (∫ t in a..b, w t) < ∫ t in a..b, w t * q t := by
    nlinarith
  have hright : (∫ t in b..c, w t * q t) < q b * (∫ t in b..c, w t) := by
    nlinarith
  have hresult := weighted_split_ratio_strict
    (∫ t in a..b, w t) (∫ t in b..c, w t)
    (∫ t in a..b, w t * q t) (∫ t in b..c, w t * q t) (q b)
    hwLpos hwRpos hleft hright
  rw [intervalIntegral.integral_add_adjacent_intervals hIqL hIqR,
    intervalIntegral.integral_add_adjacent_intervals hIwL hIwR] at hresult
  exact hresult

end MSCi.TwoSite
