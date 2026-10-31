import MSCi.TwoSite.FixedContinuationDraft
import MSCi.TwoSite.RootDraft

/-!
Uncompiled candidate C-rate recovery for the transcribed analytic map.

This builds on the generic fixed-continuation candidate and assumes the
root time and root rate have already been identified. It does not prove
the actual six-sample pair law, JC observation bridge, or full injectivity.
No Lean check has been performed.
-/

noncomputable section

namespace MSCi.TwoSite

/-- The CC formula uses a fixed root continuation after time t0. -/
theorem cc_transform_eq_fixed (p : Parameters) (z : ℝ) :
    pairTransform p .CC z =
      fixedContinuationMoment p.t0 z
        (Real.exp (-z * p.t0) * (p.rR / (p.rR + z))) p.rC := by
  simp [pairTransform, fixedContinuationMoment] <;> ring

theorem cc_tail_le_start (p : Parameters) (z : ℝ)
    (hp : Admissible p) (hz : 0 < z) :
    Real.exp (-z * p.t0) * (p.rR / (p.rR + z)) ≤ Real.exp (-z * p.t0) := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, hR⟩
  have hden : 0 < p.rR + z := by positivity
  have hratio : p.rR / (p.rR + z) ≤ 1 := (div_le_one hden).2 (by linarith)
  have he : 0 ≤ Real.exp (-z * p.t0) := le_of_lt (Real.exp_pos _)
  simpa using mul_le_mul_of_nonneg_left hratio he

/-- Once the root parameters agree, equality of CC moments identifies rC. -/
theorem c_rate_eq_of_cc_eq (p q : Parameters) (z : ℝ)
    (hp : Admissible p) (hq : Admissible q) (hz : 0 < z)
    (ht : p.t0 = q.t0) (hR : p.rR = q.rR)
    (heq : pairTransform p .CC z = pairTransform q .CC z) : p.rC = q.rC := by
  have hT : 0 < p.t0 := by
    rcases hp with ⟨hh, hh1, h10, _⟩
    linarith
  have hpC : 0 < p.rC := by
    rcases hp with ⟨_, _, _, _, _, _, _, hC, _, _⟩
    exact hC
  have hqC : 0 < q.rC := by
    rcases hq with ⟨_, _, _, _, _, _, _, hC, _, _⟩
    exact hC
  have hK := cc_tail_le_start p z hp hz
  have hmono := fixed_continuation_strictMonoOn p.t0 z
    (Real.exp (-z * p.t0) * (p.rR / (p.rR + z))) hT hz hK
  simp only [cc_transform_eq_fixed, ← ht, ← hR] at heq
  exact hmono.injOn hpC hqC heq

/-- Candidate composition with the two previously identified root moments. -/
theorem c_rate_eq_of_nineRawFeatures_eq (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q) : p.rC = q.rC := by
  have ht : p.t0 = q.t0 := rootTime_eq_of_nineRawFeatures_eq p q hp hq hF
  have hR : p.rR = q.rR := rootRate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hz : 0 < jcPairExponent := by norm_num [jcPairExponent]
  have hcc : pairTransform p .CC jcPairExponent = pairTransform q .CC jcPairExponent := by
    have h := congrFun hF (2 : Fin 9)
    simpa [nineRawFeatures] using h
  exact c_rate_eq_of_cc_eq p q jcPairExponent hp hq hz ht hR hcc

end MSCi.TwoSite
