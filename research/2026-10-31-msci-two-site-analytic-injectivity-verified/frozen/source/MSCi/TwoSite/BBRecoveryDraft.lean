import MSCi.TwoSite.BBContinuationDraft

/-!
Uncompiled candidate B-rate and analytic nine-feature injectivity assembly.

The B-rate comparison keeps one variable in both tied segments. Its proof
depends on all of the imported candidate bounds and prior recovery steps.
This is not a Lean-checked theorem, a source-process or observation-law
construction, or a proof of the separate Jacobian or interval obligations.
-/

noncomputable section

namespace MSCi.TwoSite

/-- The stay/stay continuation increases with the shared B rate. -/
theorem bb_stay_strictMonoOn (p : Parameters) (z : ℝ)
    (hp : Admissible p) (hz : 0 < z) :
    StrictMonoOn (bbStayContinuation p z) (Set.Ioi 0) := by
  intro r hr s hs hrs
  have hlen : 0 < p.t1 - p.h := sub_pos.mpr hp.2.1
  have hK := bb_ab_relative_tail_le_start p z hp hz
  have hmono := fixed_continuation_strictMonoOn (p.t1 - p.h) z
    (bbABRelativeTail p z) hlen hz hK
  unfold bbStayContinuation
  exact mul_lt_mul_of_pos_left (hmono hr hs hrs) (Real.exp_pos (-z * p.h))

theorem bb_tail_mono (p : Parameters) (z r s : ℝ)
    (hp : Admissible p) (hz : 0 < z) (hr : 0 < r) (hs : 0 < s) (hrs : r < s) :
    bbTail p z r ≤ bbTail p z s := by
  have hstay : bbStayContinuation p z r ≤ bbStayContinuation p z s :=
    le_of_lt (bb_stay_strictMonoOn p z hp hz hr hs hrs)
  have hmul := mul_le_mul_of_nonneg_left hstay (sq_nonneg (1 - p.g))
  unfold bbTail
  linarith

/-- One positive B rate appears in both segments, and the full moment increases. -/
theorem bb_forward_strictMonoOn (p : Parameters) (z : ℝ)
    (hp : Admissible p) (hz : 0 < z) :
    StrictMonoOn (bbForwardAt p z) (Set.Ioi 0) := by
  intro r hr s hs hrs
  have hK := bb_tail_le_start p z r hp hz hr
  have hfixed := fixed_continuation_strictMonoOn p.h z (bbTail p z r) hp.1 hz hK
  have hfirst := hfixed hr hs hrs
  have htail := bb_tail_mono p z r s hp hz hr hs hrs
  have hsecond : fixedContinuationMoment p.h z (bbTail p z r) s ≤
      fixedContinuationMoment p.h z (bbTail p z s) s := by
    have hmul := mul_le_mul_of_nonneg_left htail (le_of_lt (Real.exp_pos (-s * p.h)))
    unfold fixedContinuationMoment
    linarith
  simpa [bbForwardAt] using lt_of_lt_of_le hfirst hsecond

/-- The last BB coordinate recovers the B rate once the other arguments agree. -/
theorem b_rate_eq_of_nineRawFeatures_eq (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q) : p.rB = q.rB := by
  have ht := rootTime_eq_of_nineRawFeatures_eq p q hp hq hF
  have hR := rootRate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hC := c_rate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hhg := pulse_parameters_eq_of_nineRawFeatures_eq p q hp hq hF
  have hAB := ab_parameters_eq_of_nineRawFeatures_eq p q hp hq hF
  have hbb : pairTransform p .BB jcPairExponent = pairTransform q .BB jcPairExponent := by
    have h := congrFun hF (8 : Fin 9)
    simpa [nineRawFeatures] using h
  rw [bb_transform_eq_forwardAt p, bb_transform_eq_forwardAt q] at hbb
  have hsame : bbForwardAt q jcPairExponent q.rB = bbForwardAt p jcPairExponent q.rB := by
    simp only [bbForwardAt, bbTail, bbStayContinuation, bbRouteContinuation, bbABRelativeTail,
      ← hhg.1, ← hhg.2, ← hAB.1, ← ht, ← hR, ← hC, ← hAB.2]
  rw [hsame] at hbb
  have hpB : 0 < p.rB := by rcases hp with ⟨_, _, _, _, _, _, hpB, _⟩; exact hpB
  have hqB : 0 < q.rB := by rcases hq with ⟨_, _, _, _, _, _, hqB, _⟩; exact hqB
  have hz : 0 < jcPairExponent := by norm_num [jcPairExponent]
  exact (bb_forward_strictMonoOn p jcPairExponent hp hz).injOn hpB hqB hbb

/-- Candidate global injectivity of the transcribed analytic feature map. -/
theorem nineRawFeatures_injective_on_admissible (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q) : p = q := by
  have ht := rootTime_eq_of_nineRawFeatures_eq p q hp hq hF
  have hR := rootRate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hC := c_rate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hhg := pulse_parameters_eq_of_nineRawFeatures_eq p q hp hq hF
  have hAAB := a_and_ab_parameters_eq_of_nineRawFeatures_eq p q hp hq hF
  have hB := b_rate_eq_of_nineRawFeatures_eq p q hp hq hF
  cases p
  cases q
  simp_all

end MSCi.TwoSite
