import MSCi.TwoSite.CRecoveryDraft

/-!
Uncompiled candidate A-rate recovery for the transcribed formula map.

The generic upper bound below supports the AA continuation. The A-rate
recovery still depends on prior identification of the AB onset and rate;
it does not establish those facts, the actual pair law or the JC bridge.
No Lean check has been performed.
-/

noncomputable section

namespace MSCi.TwoSite

/-- A fixed continuation bounded at its start gives a moment at most one. -/
theorem fixed_continuation_le_one (L z K r : ℝ)
    (hL : 0 ≤ L) (hz : 0 < z) (hr : 0 < r) (hK : K ≤ Real.exp (-z * L)) :
    fixedContinuationMoment L z K r ≤ 1 := by
  have hden : 0 < r + z := by positivity
  have hratio : r / (r + z) ≤ 1 := (div_le_one hden).2 (by linarith)
  have hs : Real.exp (-(r + z) * L) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hprod : 0 ≤ (r + z) * L := mul_nonneg (le_of_lt hden) hL
    linarith
  have hsmall : 0 ≤ (1 - r / (r + z)) * (1 - Real.exp (-(r + z) * L)) :=
    mul_nonneg (sub_nonneg.mpr hratio) (sub_nonneg.mpr hs)
  have htail : Real.exp (-r * L) * K ≤ Real.exp (-(r + z) * L) := by
    calc
      Real.exp (-r * L) * K ≤ Real.exp (-r * L) * Real.exp (-z * L) :=
        mul_le_mul_of_nonneg_left hK (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(r + z) * L) := by
        rw [← Real.exp_add]
        congr 1
        ring
  unfold fixedContinuationMoment
  nlinarith

/-- The AA moment's conditional continuation after the A/B join. -/
def aaContinuation (p : Parameters) (z : ℝ) : ℝ :=
  Real.exp (-z * p.t1) *
    fixedContinuationMoment (p.t0 - p.t1) z
      (Real.exp (-z * (p.t0 - p.t1)) * (p.rR / (p.rR + z))) p.rAB

theorem aa_transform_eq_fixed (p : Parameters) (z : ℝ) :
    pairTransform p .AA z = fixedContinuationMoment p.t1 z (aaContinuation p z) p.rA := by
  have hexp : Real.exp (-z * p.t0) =
      Real.exp (-z * p.t1) * Real.exp (-z * (p.t0 - p.t1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp [pairTransform, fixedContinuationMoment, aaContinuation, hexp] <;> ring

theorem aa_continuation_le_start (p : Parameters) (z : ℝ)
    (hp : Admissible p) (hz : 0 < z) : aaContinuation p z ≤ Real.exp (-z * p.t1) := by
  rcases hp with ⟨_, _, h10, _, _, _, _, _, hAB, hR⟩
  have hL : 0 ≤ p.t0 - p.t1 := le_of_lt (sub_pos.mpr h10)
  have hden : 0 < p.rR + z := by positivity
  have hratio : p.rR / (p.rR + z) ≤ 1 := (div_le_one hden).2 (by linarith)
  have hbase :
      Real.exp (-z * (p.t0 - p.t1)) * (p.rR / (p.rR + z)) ≤
        Real.exp (-z * (p.t0 - p.t1)) := by
    have he : 0 ≤ Real.exp (-z * (p.t0 - p.t1)) := le_of_lt (Real.exp_pos _)
    simpa using mul_le_mul_of_nonneg_left hratio he
  have hseg := fixed_continuation_le_one (p.t0 - p.t1) z
    (Real.exp (-z * (p.t0 - p.t1)) * (p.rR / (p.rR + z))) p.rAB hL hz hAB hbase
  have he : 0 ≤ Real.exp (-z * p.t1) := le_of_lt (Real.exp_pos _)
  simpa [aaContinuation] using mul_le_mul_of_nonneg_left hseg he

/-- Once root and AB continuation parameters agree, AA identifies rA. -/
theorem a_rate_eq_of_aa_eq (p q : Parameters) (z : ℝ)
    (hp : Admissible p) (hq : Admissible q) (hz : 0 < z)
    (ht1 : p.t1 = q.t1) (ht0 : p.t0 = q.t0)
    (hAB : p.rAB = q.rAB) (hR : p.rR = q.rR)
    (heq : pairTransform p .AA z = pairTransform q .AA z) : p.rA = q.rA := by
  have hT : 0 < p.t1 := by
    rcases hp with ⟨hh, hh1, _⟩
    linarith
  have hpA : 0 < p.rA := by
    rcases hp with ⟨_, _, _, _, _, hA, _⟩
    exact hA
  have hqA : 0 < q.rA := by
    rcases hq with ⟨_, _, _, _, _, hA, _⟩
    exact hA
  have hK := aa_continuation_le_start p z hp hz
  have hmono := fixed_continuation_strictMonoOn p.t1 z (aaContinuation p z) hT hz hK
  simp only [aa_transform_eq_fixed, aaContinuation, ← ht1, ← ht0, ← hAB, ← hR] at heq
  exact hmono.injOn hpA hqA heq

/-- Candidate composition with root recovery and the later AB prerequisites. -/
theorem a_rate_eq_of_nineRawFeatures_eq (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q)
    (ht1 : p.t1 = q.t1) (hAB : p.rAB = q.rAB) : p.rA = q.rA := by
  have ht0 : p.t0 = q.t0 := rootTime_eq_of_nineRawFeatures_eq p q hp hq hF
  have hR : p.rR = q.rR := rootRate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hz : 0 < jcPairExponent := by norm_num [jcPairExponent]
  have haa : pairTransform p .AA jcPairExponent = pairTransform q .AA jcPairExponent := by
    have h := congrFun hF (7 : Fin 9)
    simpa [nineRawFeatures] using h
  exact a_rate_eq_of_aa_eq p q jcPairExponent hp hq hz ht1 ht0 hAB hR haa

end MSCi.TwoSite
