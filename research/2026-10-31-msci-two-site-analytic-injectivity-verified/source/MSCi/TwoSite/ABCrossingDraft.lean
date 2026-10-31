import MSCi.TwoSite.ABContinuationDraft

/-!
Uncompiled bounded-integral candidate for the AB single-crossing argument.

The common root tail is represented explicitly rather than by an improper
integral. This is an auxiliary result about a supplied continuous difference
and a supplied crossing: the actual AB survival difference, crossing existence,
and moment-to-integral identity still have to be constructed and proved.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace MSCi.TwoSite

def abCrossTerm (D : ℝ → ℝ) (c s t : ℝ) : ℝ :=
  Real.exp (-c * t) * (Real.exp (-c * t) - Real.exp (-c * s)) * D t

/-- A strict negative-to-positive crossing separates the two weighted integrals. -/
theorem ab_bounded_crossing_separates (D : ℝ → ℝ) (T R c s x : ℝ)
    (hD : Continuous D) (hR : 0 < R) (hc : 0 < c)
    (hs0 : 0 < s) (hsT : s < T) (hx0 : 0 ≤ x) (hxT : x ≤ T) (hxs : x < s)
    (hxneg : D x < 0)
    (hleft : ∀ t ∈ Set.Icc 0 T, t < s → D t ≤ 0)
    (hright : ∀ t ∈ Set.Icc 0 T, s < t → 0 ≤ D t)
    (hend : 0 ≤ D T)
    (hzero : (∫ t in (0 : ℝ)..T, Real.exp (-c * t) * D t) +
        Real.exp (-c * T) * D T / (R + c) = 0) :
    (∫ t in (0 : ℝ)..T, Real.exp (-(2 * c) * t) * D t) +
        Real.exp (-(2 * c) * T) * D T / (R + 2 * c) < 0 := by
  have h0T : (0 : ℝ) < T := lt_trans hs0 hsT
  have hnonpos : ∀ t ∈ Set.Icc (0 : ℝ) T, abCrossTerm D c s t ≤ 0 := by
    intro t ht
    rcases lt_trichotomy t s with hlt | heq | hgt
    · have hprod : 0 < c * (s - t) := mul_pos hc (sub_pos.mpr hlt)
      have he : Real.exp (-c * s) < Real.exp (-c * t) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      have hfac : 0 ≤ Real.exp (-c * t) * (Real.exp (-c * t) - Real.exp (-c * s)) :=
        mul_nonneg (le_of_lt (Real.exp_pos _)) (sub_nonneg.mpr (le_of_lt he))
      exact mul_nonpos_of_nonneg_of_nonpos hfac (hleft t ht hlt)
    · subst t
      simp [abCrossTerm]
    · have hprod : 0 < c * (t - s) := mul_pos hc (sub_pos.mpr hgt)
      have he : Real.exp (-c * t) < Real.exp (-c * s) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      have hfac : Real.exp (-c * t) * (Real.exp (-c * t) - Real.exp (-c * s)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) (sub_nonpos.mpr (le_of_lt he))
      exact mul_nonpos_of_nonpos_of_nonneg hfac (hright t ht hgt)
  have hneg : abCrossTerm D c s x < 0 := by
    have hprod : 0 < c * (s - x) := mul_pos hc (sub_pos.mpr hxs)
    have he : Real.exp (-c * s) < Real.exp (-c * x) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    have hfac : 0 < Real.exp (-c * x) * (Real.exp (-c * x) - Real.exp (-c * s)) :=
      mul_pos (Real.exp_pos _) (sub_pos.mpr he)
    exact mul_neg_of_pos_of_neg hfac hxneg
  have hcont : Continuous (abCrossTerm D c s) := by
    unfold abCrossTerm
    fun_prop
  have hintneg : (∫ t in (0 : ℝ)..T, abCrossTerm D c s t) < 0 := by
    have hpos : 0 < ∫ t in (0 : ℝ)..T, -abCrossTerm D c s t := by
      apply intervalIntegral.integral_pos h0T hcont.neg.continuousOn
      · intro t ht
        exact neg_nonneg.mpr (hnonpos t ⟨le_of_lt ht.1, ht.2⟩)
      · exact ⟨x, ⟨hx0, hxT⟩, neg_pos.mpr hneg⟩
    rw [intervalIntegral.integral_neg] at hpos
    linarith
  have he2 (t : ℝ) : Real.exp (-(2 * c) * t) = Real.exp (-c * t) * Real.exp (-c * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hI1 : IntervalIntegrable (fun t : ℝ => Real.exp (-c * t) * D t) volume 0 T := by
    have h : Continuous (fun t : ℝ => Real.exp (-c * t) * D t) := by fun_prop
    exact h.intervalIntegrable 0 T
  have hI2 : IntervalIntegrable (fun t : ℝ => Real.exp (-(2 * c) * t) * D t) volume 0 T := by
    have h : Continuous (fun t : ℝ => Real.exp (-(2 * c) * t) * D t) := by fun_prop
    exact h.intervalIntegrable 0 T
  have hint : (∫ t in (0 : ℝ)..T, abCrossTerm D c s t) =
      (∫ t in (0 : ℝ)..T, Real.exp (-(2 * c) * t) * D t) -
        Real.exp (-c * s) * (∫ t in (0 : ℝ)..T, Real.exp (-c * t) * D t) := by
    calc
      (∫ t in (0 : ℝ)..T, abCrossTerm D c s t) =
          ∫ t in (0 : ℝ)..T, (Real.exp (-(2 * c) * t) * D t -
            (Real.exp (-c * t) * D t) * Real.exp (-c * s)) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only [abCrossTerm]
        rw [he2 t]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hI2 (hI1.mul_const _),
          intervalIntegral.integral_mul_const]
        ring
  have hd1 : 0 < R + c := by positivity
  have hd2 : 0 < R + 2 * c := by positivity
  have heT : Real.exp (-c * T) < Real.exp (-c * s) := by
    have hprod : 0 < c * (T - s) := mul_pos hc (sub_pos.mpr hsT)
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hden : R + c < R + 2 * c := by linarith
  have hfrac : Real.exp (-c * T) / (R + 2 * c) <
      Real.exp (-c * s) / (R + c) := by
    apply (div_lt_div_iff₀ hd2 hd1).2
    exact lt_trans (mul_lt_mul_of_pos_right heT hd1)
      (mul_lt_mul_of_pos_left hden (Real.exp_pos _))
  have htailnonpos : Real.exp (-c * T) * D T *
      (Real.exp (-c * T) / (R + 2 * c) - Real.exp (-c * s) / (R + c)) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (le_of_lt (Real.exp_pos _)) hend) (sub_nonpos.mpr (le_of_lt hfrac))
  have htail : Real.exp (-(2 * c) * T) * D T / (R + 2 * c) -
      Real.exp (-c * s) * (Real.exp (-c * T) * D T / (R + c)) =
      Real.exp (-c * T) * D T *
        (Real.exp (-c * T) / (R + 2 * c) - Real.exp (-c * s) / (R + c)) := by
    rw [he2 T]
    ring
  have hzmul := congrArg (fun y : ℝ => Real.exp (-c * s) * y) hzero
  have hdecomp :
      (∫ t in (0 : ℝ)..T, Real.exp (-(2 * c) * t) * D t) +
          Real.exp (-(2 * c) * T) * D T / (R + 2 * c) =
        ((∫ t in (0 : ℝ)..T, Real.exp (-(2 * c) * t) * D t) -
          Real.exp (-c * s) * (∫ t in (0 : ℝ)..T, Real.exp (-c * t) * D t)) +
        (Real.exp (-(2 * c) * T) * D T / (R + 2 * c) -
          Real.exp (-c * s) * (Real.exp (-c * T) * D T / (R + c))) := by
    nlinarith [hzmul]
  rw [hdecomp, ← hint, htail]
  exact add_neg_of_neg_of_nonpos hintneg htailnonpos

end MSCi.TwoSite
