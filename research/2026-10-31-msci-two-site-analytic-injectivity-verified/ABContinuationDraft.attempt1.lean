import MSCi.TwoSite.BCRecoveryDraft
import MSCi.TwoSite.ARecoveryDraft

/-!
Uncompiled candidate AB reduction for the transcribed analytic map.

This reduces the two AB features to the two shifted-route moments after
the root and pulse probability are identified. It also proposes strict
rate recovery at a fixed onset. It does not prove the global two-moment
single-crossing step, the source pair law or the observation bridge.
-/

noncomputable section

namespace MSCi.TwoSite

/-- The AB formula is a root route plus a shifted ancestral route. -/
theorem ab_transform_split (p : Parameters) (z : ℝ) :
    pairTransform p .AB z = p.g * rootMoment p.t0 p.rR z +
      (1 - p.g) * pulseShiftedMoment p.t0 p.rR p.rAB z p.t1 := by
  simp [pairTransform, pulseShiftedMoment, rootMoment] <;> ring

/-- At fixed root and pulse probability, equal AB moments give equal route moments. -/
theorem ab_shifted_eq_of_ab_eq (p q : Parameters) (z : ℝ)
    (hp : Admissible p) (ht : p.t0 = q.t0) (hR : p.rR = q.rR)
    (hg : p.g = q.g)
    (heq : pairTransform p .AB z = pairTransform q .AB z) :
    pulseShiftedMoment p.t0 p.rR p.rAB z p.t1 =
      pulseShiftedMoment q.t0 q.rR q.rAB z q.t1 := by
  have hg1 : p.g < 1 := by rcases hp with ⟨_, _, _, _, hg1, _⟩; exact hg1
  have hmix : 1 - p.g ≠ 0 := ne_of_gt (sub_pos.mpr hg1)
  rw [ab_transform_split p, ab_transform_split q, ← ht, ← hR, ← hg] at heq
  rw [← ht, ← hR]
  apply mul_left_cancel₀ hmix
  linarith

/-- Shifted continuation is a fixed-continuation moment times its onset factor. -/
theorem ab_shifted_eq_fixed (T R r z a : ℝ) :
    pulseShiftedMoment T R r z a = Real.exp (-z * a) *
      fixedContinuationMoment (T - a) z
        (Real.exp (-z * (T - a)) * (R / (R + z))) r := by
  have he : Real.exp (-z * T) =
      Real.exp (-z * a) * Real.exp (-z * (T - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp [pulseShiftedMoment, rootMoment, fixedContinuationMoment, he] <;> ring

/-- For one fixed onset, positive ancestral rate is identified by one moment. -/
theorem ab_rate_eq_at_fixed_onset (T R r s z a : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hs : 0 < s) (hz : 0 < z) (ha : a < T)
    (heq : pulseShiftedMoment T R r z a = pulseShiftedMoment T R s z a) : r = s := by
  have hL : 0 < T - a := sub_pos.mpr ha
  have hden : 0 < R + z := by positivity
  have hratio : R / (R + z) ≤ 1 := (div_le_one hden).2 (by linarith)
  have hK : Real.exp (-z * (T - a)) * (R / (R + z)) ≤
      Real.exp (-z * (T - a)) := by
    have h := mul_le_mul_of_nonneg_left hratio (le_of_lt (Real.exp_pos (-z * (T - a))))
    simpa using h
  have hmono := fixed_continuation_strictMonoOn (T - a) z
    (Real.exp (-z * (T - a)) * (R / (R + z))) hL hz hK
  rw [ab_shifted_eq_fixed T R r z a, ab_shifted_eq_fixed T R s z a] at heq
  have hfixed : fixedContinuationMoment (T - a) z
        (Real.exp (-z * (T - a)) * (R / (R + z))) r =
      fixedContinuationMoment (T - a) z
        (Real.exp (-z * (T - a)) * (R / (R + z))) s :=
    (mul_left_cancel₀ (ne_of_gt (Real.exp_pos (-z * a)))) heq
  exact hmono.injOn hr hs hfixed

/-- The two AB route moments are inherited from equality of the nine features. -/
theorem ab_shifted_moments_eq_of_nineRawFeatures_eq (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q) :
    pulseShiftedMoment p.t0 p.rR p.rAB jcPairExponent p.t1 =
        pulseShiftedMoment q.t0 q.rR q.rAB jcPairExponent q.t1 ∧
      pulseShiftedMoment p.t0 p.rR p.rAB (2 * jcPairExponent) p.t1 =
        pulseShiftedMoment q.t0 q.rR q.rAB (2 * jcPairExponent) q.t1 := by
  have ht := rootTime_eq_of_nineRawFeatures_eq p q hp hq hF
  have hR := rootRate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hg := (pulse_parameters_eq_of_nineRawFeatures_eq p q hp hq hF).2
  have h1 : pairTransform p .AB jcPairExponent = pairTransform q .AB jcPairExponent := by
    have h := congrFun hF (5 : Fin 9)
    simpa [nineRawFeatures] using h
  have h2 : pairTransform p .AB (2 * jcPairExponent) =
      pairTransform q .AB (2 * jcPairExponent) := by
    have h := congrFun hF (6 : Fin 9)
    simpa [nineRawFeatures] using h
  exact ⟨ab_shifted_eq_of_ab_eq p q jcPairExponent hp ht hR hg h1,
    ab_shifted_eq_of_ab_eq p q (2 * jcPairExponent) hp ht hR hg h2⟩

/-- The remaining global step is only needed when the AB onsets differ. -/
theorem ab_rate_eq_of_features_and_onset_eq (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q) (ha : p.t1 = q.t1) : p.rAB = q.rAB := by
  have ht := rootTime_eq_of_nineRawFeatures_eq p q hp hq hF
  have hR := rootRate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hfirst := (ab_shifted_moments_eq_of_nineRawFeatures_eq p q hp hq hF).1
  rw [← ht, ← hR, ← ha] at hfirst
  have hpr : 0 < p.rAB := by rcases hp with ⟨_, _, _, _, _, _, _, _, hpr, _⟩; exact hpr
  have hqr : 0 < q.rAB := by rcases hq with ⟨_, _, _, _, _, _, _, _, hqr, _⟩; exact hqr
  have hpR : 0 < p.rR := by rcases hp with ⟨_, _, _, _, _, _, _, _, _, hpR⟩; exact hpR
  have hz : 0 < jcPairExponent := by norm_num [jcPairExponent]
  exact ab_rate_eq_at_fixed_onset p.t0 p.rR p.rAB q.rAB jcPairExponent p.t1
    hpR hpr hqr hz hp.2.2.1 hfirst

end MSCi.TwoSite
