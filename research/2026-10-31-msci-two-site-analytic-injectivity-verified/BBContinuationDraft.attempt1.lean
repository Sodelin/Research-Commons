import MSCi.TwoSite.ABRecoveryDraft

/-!
Uncompiled candidate decomposition of the BB formula with a tied B rate.

The stay/stay continuation uses the same candidate B rate as the pre-pulse
segment. Route/route and split continuations are independent of that rate.
The representation is an algebraic claim about the transcribed formula, not
a construction or projection theorem for the six-sample stochastic process.
-/

noncomputable section

namespace MSCi.TwoSite

def bbRootTail (L R z : ℝ) : ℝ :=
  Real.exp (-z * L) * (R / (R + z))

def bbABRelativeTail (p : Parameters) (z : ℝ) : ℝ :=
  Real.exp (-z * (p.t1 - p.h)) *
    fixedContinuationMoment (p.t0 - p.t1) z
      (bbRootTail (p.t0 - p.t1) p.rR z) p.rAB

def bbStayContinuation (p : Parameters) (z r : ℝ) : ℝ :=
  Real.exp (-z * p.h) *
    fixedContinuationMoment (p.t1 - p.h) z (bbABRelativeTail p z) r

def bbRouteContinuation (p : Parameters) (z : ℝ) : ℝ :=
  Real.exp (-z * p.h) *
    fixedContinuationMoment (p.t0 - p.h) z
      (bbRootTail (p.t0 - p.h) p.rR z) p.rC

def bbTail (p : Parameters) (z r : ℝ) : ℝ :=
  (1 - p.g) ^ 2 * bbStayContinuation p z r +
    p.g ^ 2 * bbRouteContinuation p z + 2 * p.g * (1 - p.g) * rootMoment p.t0 p.rR z

def bbForwardAt (p : Parameters) (z r : ℝ) : ℝ :=
  fixedContinuationMoment p.h z (bbTail p z r) r

/-- The BB formula uses rB in both pre-pulse and stay/stay segments. -/
theorem bb_transform_eq_forwardAt (p : Parameters) (z : ℝ) :
    pairTransform p .BB z = bbForwardAt p z p.rB := by
  have he₁ : Real.exp (-z * p.t1) =
      Real.exp (-z * p.h) * Real.exp (-z * (p.t1 - p.h)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he₂ : Real.exp (-z * p.t0) =
      Real.exp (-z * p.h) * Real.exp (-z * (p.t1 - p.h)) *
        Real.exp (-z * (p.t0 - p.t1)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have he₃ : Real.exp (-z * (p.t0 - p.h)) =
      Real.exp (-z * (p.t1 - p.h)) * Real.exp (-z * (p.t0 - p.t1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlen : p.t1 - p.h + (p.t0 - p.t1) = p.t0 - p.h := by ring
  simp [pairTransform, bbForwardAt, bbTail, bbStayContinuation, bbRouteContinuation,
    bbABRelativeTail, bbRootTail, fixedContinuationMoment, rootMoment, hlen, he₃, ← he₁, ← he₂] <;> ring

theorem bb_root_tail_le_start (L R z : ℝ) (hR : 0 < R) (hz : 0 < z) :
    bbRootTail L R z ≤ Real.exp (-z * L) := by
  have hden : 0 < R + z := by positivity
  have hratio : R / (R + z) ≤ 1 := (div_le_one hden).2 (by linarith)
  have h := mul_le_mul_of_nonneg_left hratio (le_of_lt (Real.exp_pos (-z * L)))
  simpa [bbRootTail] using h

theorem bb_ab_relative_tail_le_start (p : Parameters) (z : ℝ)
    (hp : Admissible p) (hz : 0 < z) :
    bbABRelativeTail p z ≤ Real.exp (-z * (p.t1 - p.h)) := by
  have hlen : 0 ≤ p.t0 - p.t1 := le_of_lt (sub_pos.mpr hp.2.2.1)
  have hR : 0 < p.rR := by rcases hp with ⟨_, _, _, _, _, _, _, _, _, hR⟩; exact hR
  have hAB : 0 < p.rAB := by rcases hp with ⟨_, _, _, _, _, _, _, _, hAB, _⟩; exact hAB
  have hK := bb_root_tail_le_start (p.t0 - p.t1) p.rR z hR hz
  have hseg := fixed_continuation_le_one (p.t0 - p.t1) z
    (bbRootTail (p.t0 - p.t1) p.rR z) p.rAB hlen hz hAB hK
  have h := mul_le_mul_of_nonneg_left hseg (le_of_lt (Real.exp_pos (-z * (p.t1 - p.h))))
  simpa [bbABRelativeTail] using h

theorem bb_stay_continuation_le_start (p : Parameters) (z r : ℝ)
    (hp : Admissible p) (hz : 0 < z) (hr : 0 < r) :
    bbStayContinuation p z r ≤ Real.exp (-z * p.h) := by
  have hlen : 0 ≤ p.t1 - p.h := le_of_lt (sub_pos.mpr hp.2.1)
  have hK := bb_ab_relative_tail_le_start p z hp hz
  have hseg := fixed_continuation_le_one (p.t1 - p.h) z (bbABRelativeTail p z) r hlen hz hr hK
  have h := mul_le_mul_of_nonneg_left hseg (le_of_lt (Real.exp_pos (-z * p.h)))
  simpa [bbStayContinuation] using h

theorem bb_route_continuation_le_start (p : Parameters) (z : ℝ)
    (hp : Admissible p) (hz : 0 < z) :
    bbRouteContinuation p z ≤ Real.exp (-z * p.h) := by
  have hhT : p.h < p.t0 := lt_trans hp.2.1 hp.2.2.1
  have hlen : 0 ≤ p.t0 - p.h := le_of_lt (sub_pos.mpr hhT)
  have hR : 0 < p.rR := by rcases hp with ⟨_, _, _, _, _, _, _, _, _, hR⟩; exact hR
  have hC : 0 < p.rC := by rcases hp with ⟨_, _, _, _, _, _, _, hC, _, _⟩; exact hC
  have hK := bb_root_tail_le_start (p.t0 - p.h) p.rR z hR hz
  have hseg := fixed_continuation_le_one (p.t0 - p.h) z
    (bbRootTail (p.t0 - p.h) p.rR z) p.rC hlen hz hC hK
  have h := mul_le_mul_of_nonneg_left hseg (le_of_lt (Real.exp_pos (-z * p.h)))
  simpa [bbRouteContinuation] using h

theorem bb_tail_le_start (p : Parameters) (z r : ℝ)
    (hp : Admissible p) (hz : 0 < z) (hr : 0 < r) :
    bbTail p z r ≤ Real.exp (-z * p.h) := by
  have hg : 0 < p.g := by rcases hp with ⟨_, _, _, hg, _⟩; exact hg
  have hg1 : p.g < 1 := by rcases hp with ⟨_, _, _, _, hg1, _⟩; exact hg1
  have hR : 0 < p.rR := by rcases hp with ⟨_, _, _, _, _, _, _, _, _, hR⟩; exact hR
  have hhT : p.h ≤ p.t0 := le_of_lt (lt_trans hp.2.1 hp.2.2.1)
  have hstay := bb_stay_continuation_le_start p z r hp hz hr
  have hroute := bb_route_continuation_le_start p z hp hz
  have hsplit : rootMoment p.t0 p.rR z ≤ Real.exp (-z * p.h) :=
    le_of_lt (root_moment_lt_exp_at p.t0 p.rR z p.h hR hz hhT)
  have hss : 0 ≤ (1 - p.g) ^ 2 := sq_nonneg _
  have hcc : 0 ≤ p.g ^ 2 := sq_nonneg _
  have hstayProb : 0 < 1 - p.g := sub_pos.mpr hg1
  have hsp : 0 ≤ 2 * p.g * (1 - p.g) := by positivity
  have hs := mul_le_mul_of_nonneg_left hstay hss
  have hc := mul_le_mul_of_nonneg_left hroute hcc
  have hp' := mul_le_mul_of_nonneg_left hsplit hsp
  have hsum : (1 - p.g) ^ 2 + p.g ^ 2 + 2 * p.g * (1 - p.g) = 1 := by ring
  unfold bbTail
  nlinarith

end MSCi.TwoSite
