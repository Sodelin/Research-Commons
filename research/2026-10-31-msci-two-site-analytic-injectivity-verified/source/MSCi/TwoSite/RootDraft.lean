import MSCi.TwoSite.ForwardDraft

/-!
Uncompiled candidate for the root-rate step in the two-site hand proof.

This source has not been elaborated or kernel checked. Its algebra concerns
the declared root-moment formulas; linking those formulas to the six-sample
process and the JC observation law remains a separate obligation.
-/

noncomputable section

namespace MSCi.TwoSite

/-- Pair moment for a root-only coalescence beginning at time `t`. -/
def rootMoment (t r z : ℝ) : ℝ :=
  Real.exp (-z * t) * (r / (r + z))

/-- The AC branch of the transcribed forward map is the root-only formula. -/
theorem ac_transform_eq_rootMoment (p : Parameters) (z : ℝ) :
    pairTransform p .AC z = rootMoment p.t0 p.rR z := by
  rfl

/-- Ratio of the second root moment to the square of the first. -/
def rootRatio (r c : ℝ) : ℝ :=
  (r + c) ^ 2 / (r * (r + 2 * c))

theorem rootRatio_eq_one_add (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    rootRatio r c = 1 + c ^ 2 / (r * (r + 2 * c)) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrc0 : r + 2 * c ≠ 0 := ne_of_gt (by positivity)
  unfold rootRatio
  field_simp [hr0, hrc0] <;> ring

/-- Increasing the positive root rate strictly decreases the ratio. -/
theorem rootRatio_strictAnti (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a < b) :
    rootRatio b c < rootRatio a c := by
  have haden : 0 < a * (a + 2 * c) := by positivity
  have hbden : 0 < b * (b + 2 * c) := by positivity
  have hdiff : 0 < b - a := sub_pos.mpr hab
  have hsum : 0 < a + b + 2 * c := by positivity
  have hprod : 0 < (b - a) * (a + b + 2 * c) := mul_pos hdiff hsum
  have hden : a * (a + 2 * c) < b * (b + 2 * c) := by nlinarith
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hfrac : c ^ 2 / (b * (b + 2 * c)) < c ^ 2 / (a * (a + 2 * c)) := by
    apply (div_lt_div_iff₀ hbden haden).2
    exact mul_lt_mul_of_pos_left hden hc2
  rw [rootRatio_eq_one_add b c hb hc, rootRatio_eq_one_add a c ha hc]
  linarith

theorem rootRatio_injective (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (heq : rootRatio a c = rootRatio b c) : a = b := by
  rcases lt_trichotomy a b with hlt | heq' | hgt
  · have h := rootRatio_strictAnti a b c ha hb hc hlt
    linarith
  · exact heq'
  · have h := rootRatio_strictAnti b a c hb ha hc hgt
    linarith

/-- The root time cancels in the ratio of the two root moments. -/
theorem rootMoments_ratio (t r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    rootMoment t r (2 * c) / (rootMoment t r c) ^ 2 = rootRatio r c := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrc0 : r + c ≠ 0 := ne_of_gt (by positivity)
  have hr2c0 : r + 2 * c ≠ 0 := ne_of_gt (by positivity)
  have he0 : Real.exp (-c * t) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have he2 : Real.exp (-(2 * c) * t) = Real.exp (-c * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1 <;> ring
  unfold rootMoment rootRatio
  rw [he2]
  field_simp [hr0, hrc0, hr2c0, he0] <;> ring

/-- Equality of the two declared root moments identifies the root rate. -/
theorem rootRate_eq_of_moments_eq (t t' r r' c : ℝ)
    (hr : 0 < r) (hr' : 0 < r') (hc : 0 < c)
    (h1 : rootMoment t r c = rootMoment t' r' c)
    (h2 : rootMoment t r (2 * c) = rootMoment t' r' (2 * c)) :
    r = r' := by
  have hquot : rootMoment t r (2 * c) / (rootMoment t r c) ^ 2 =
      rootMoment t' r' (2 * c) / (rootMoment t' r' c) ^ 2 := by
    rw [h1, h2]
  rw [rootMoments_ratio t r c hr hc, rootMoments_ratio t' r' c hr' hc] at hquot
  exact rootRatio_injective r r' c hr hr' hc hquot

/-- Equality of the draft's nine features forces the root rates to agree. -/
theorem rootRate_eq_of_nineRawFeatures_eq (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q) : p.rR = q.rR := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, hpR⟩
  rcases hq with ⟨_, _, _, _, _, _, _, _, _, hqR⟩
  have hc : 0 < jcPairExponent := by norm_num [jcPairExponent]
  have h1 : rootMoment p.t0 p.rR jcPairExponent =
      rootMoment q.t0 q.rR jcPairExponent := by
    have h := congrFun hF (0 : Fin 9)
    simpa [nineRawFeatures, ac_transform_eq_rootMoment] using h
  have h2 : rootMoment p.t0 p.rR (2 * jcPairExponent) =
      rootMoment q.t0 q.rR (2 * jcPairExponent) := by
    have h := congrFun hF (1 : Fin 9)
    simpa [nineRawFeatures, ac_transform_eq_rootMoment] using h
  exact rootRate_eq_of_moments_eq p.t0 q.t0 p.rR q.rR jcPairExponent hpR hqR hc h1 h2

/-- With the root rate fixed, the first root moment identifies its onset. -/
theorem rootTime_eq_of_rootMoment_eq (t t' r c : ℝ)
    (hr : 0 < r) (hc : 0 < c)
    (h : rootMoment t r c = rootMoment t' r c) : t = t' := by
  have hfac : 0 < r / (r + c) := by positivity
  have hprod : (Real.exp (-c * t) - Real.exp (-c * t')) * (r / (r + c)) = 0 := by
    dsimp [rootMoment] at h
    nlinarith
  have hdiff : Real.exp (-c * t) - Real.exp (-c * t') = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hfac)
  have hexp : Real.exp (-c * t) = Real.exp (-c * t') := by linarith
  have hlinear : -c * t = -c * t' := Real.exp_injective hexp
  have hprod' : c * (t - t') = 0 := by nlinarith
  have hdiff' : t - t' = 0 := (mul_eq_zero.mp hprod').resolve_left (ne_of_gt hc)
  linarith

/-- Equality of the draft's nine features also forces root times to agree. -/
theorem rootTime_eq_of_nineRawFeatures_eq (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q) : p.t0 = q.t0 := by
  have hR : p.rR = q.rR := rootRate_eq_of_nineRawFeatures_eq p q hp hq hF
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, hpR⟩
  have hc : 0 < jcPairExponent := by norm_num [jcPairExponent]
  have h1 : rootMoment p.t0 p.rR jcPairExponent =
      rootMoment q.t0 q.rR jcPairExponent := by
    have h := congrFun hF (0 : Fin 9)
    simpa [nineRawFeatures, ac_transform_eq_rootMoment] using h
  rw [← hR] at h1
  exact rootTime_eq_of_rootMoment_eq p.t0 q.t0 p.rR jcPairExponent hpR hc h1

end MSCi.TwoSite
