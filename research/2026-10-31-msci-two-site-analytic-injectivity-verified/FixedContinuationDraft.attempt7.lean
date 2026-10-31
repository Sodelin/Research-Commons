import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import MSCi.TwoSite.ForwardDraft

/-!
Uncompiled candidate calculus for the fixed-continuation rate argument.

This generic lemma is intended to support, not replace, the CC and AA
source-specific recovery steps. It does not instantiate their continuation
bounds or cover the BB continuation that depends on the tied B rate. No Lean
check or source-process correspondence has been established.
-/

noncomputable section

namespace MSCi.TwoSite

/-- Pre-continuation pair moment with a fixed global-time tail transform. -/
def fixedContinuationMoment (L z K r : ℝ) : ℝ :=
  r / (r + z) * (1 - Real.exp (-(r + z) * L)) + Real.exp (-r * L) * K

/-- Proposed derivative, arranged into a positive and a nonnegative term. -/
def fixedContinuationDerivative (L z K r : ℝ) : ℝ :=
  z / (r + z) ^ 2 * (1 - (1 + (r + z) * L) * Real.exp (-(r + z) * L)) +
    L * Real.exp (-r * L) * (Real.exp (-z * L) - K)

theorem exponential_tail_bracket_pos (x : ℝ) (hx : 0 < x) :
    0 < 1 - (1 + x) * Real.exp (-x) := by
  have he : 1 + x < Real.exp x := by
    have h := Real.add_one_lt_exp (ne_of_gt hx)
    linarith
  have hdiv : (1 + x) / Real.exp x < 1 :=
    (div_lt_one (Real.exp_pos x)).2 he
  rw [Real.exp_neg, ← div_eq_mul_inv]
  linarith

theorem fixed_continuation_derivative_pos (L z K r : ℝ)
    (hL : 0 < L) (hz : 0 < z) (hr : 0 < r) (hK : K ≤ Real.exp (-z * L)) :
    0 < fixedContinuationDerivative L z K r := by
  have hx : 0 < (r + z) * L := by positivity
  have hbr := exponential_tail_bracket_pos ((r + z) * L) hx
  have hcoef : 0 < z / (r + z) ^ 2 := by positivity
  have htail : 0 ≤ L * Real.exp (-r * L) * (Real.exp (-z * L) - K) := by
    have hK' : 0 ≤ Real.exp (-z * L) - K := sub_nonneg.mpr hK
    positivity
  unfold fixedContinuationDerivative
  exact add_pos_of_pos_of_nonneg (mul_pos hcoef (by simpa only [neg_mul] using hbr)) htail

theorem fixed_continuation_hasDerivAt (L z K r : ℝ)
    (hz : 0 < z) (hr : 0 < r) :
    HasDerivAt (fixedContinuationMoment L z K) (fixedContinuationDerivative L z K r) r := by
  have hne : r + z ≠ 0 := ne_of_gt (by positivity)
  have hid : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id' r
  have hden := hid.add_const z
  have hquot := hid.div hden hne
  have harg := hden.neg.mul_const L
  have he := harg.exp
  have htail := (hid.neg.mul_const L).exp
  have hsum := (hquot.mul (he.const_sub 1)).add (htail.mul_const K)
  have hexp : Real.exp (-(r + z) * L) = Real.exp (-r * L) * Real.exp (-z * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  convert hsum using 1 <;>
    (try dsimp [fixedContinuationMoment, fixedContinuationDerivative]) <;>
    (try rw [hexp]) <;> (try field_simp [hne]) <;> first | rfl | ring

theorem fixed_continuation_strictMonoOn (L z K : ℝ)
    (hL : 0 < L) (hz : 0 < z) (hK : K ≤ Real.exp (-z * L)) :
    StrictMonoOn (fixedContinuationMoment L z K) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro r hr
    exact (fixed_continuation_hasDerivAt L z K r hz hr).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : r ∈ Set.Ioi (0 : ℝ) := interior_subset hr
    rw [(fixed_continuation_hasDerivAt L z K r hz hr').deriv]
    exact fixed_continuation_derivative_pos L z K r hL hz hr' hK

end MSCi.TwoSite
