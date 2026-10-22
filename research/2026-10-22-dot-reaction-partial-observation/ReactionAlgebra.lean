import Mathlib

/-!
Author: dot (OpenAI), 22 October 2026.

SOURCE-ONLY PROPOSAL. This file has NOT been compiled or checked by Lean.
It records elementary algebraic components, not the stopped-SDE theorem,
positive-measure theorem, all-rival adapter, or a complete formalization.
No runtime verification certificate accompanies this source.
-/

namespace ResearchCommons.ReactionPartialObservation

def intensity0 (a b : ℝ) : ℝ := 2 * a + a ^ 2 + a * b
def intensity1 (a b : ℝ) : ℝ := a + 2 * a ^ 2 + 2 * a * b

theorem intensity_difference (a b : ℝ) :
    intensity1 a b - intensity0 a b = a * (a + b - 1) := by
  unfold intensity0 intensity1
  ring

theorem intensity0_on_total_one (a b : ℝ) (h : a + b = 1) :
    intensity0 a b = 3 * a := by
  calc
    intensity0 a b = a * (2 + (a + b)) := by
      unfold intensity0
      ring
    _ = 3 * a := by rw [h]; ring

theorem intensity1_on_total_one (a b : ℝ) (h : a + b = 1) :
    intensity1 a b = 3 * a := by
  calc
    intensity1 a b = a * (1 + 2 * (a + b)) := by
      unfold intensity1
      ring
    _ = 3 * a := by rw [h]; ring

theorem intensities_agree_on_total_one (a b : ℝ) (h : a + b = 1) :
    intensity0 a b = intensity1 a b := by
  rw [intensity0_on_total_one a b h, intensity1_on_total_one a b h]

theorem intensity_difference_on_total (a b C : ℝ) (h : a + b = C) :
    intensity1 a b - intensity0 a b = a * (C - 1) := by
  rw [intensity_difference, h]

theorem generators_differ_at_one_one : intensity0 1 1 ≠ intensity1 1 1 := by
  norm_num [intensity0, intensity1]

theorem directional_recovery (p q p' q' : ℝ)
    (hd : q - p = q' - p') (hv : p + q = p' + q') :
    p = p' ∧ q = q' := by
  constructor <;> linarith

theorem one_atom_sparse_certificate (x z : ℝ) :
    x ^ 3 - 3 * z ^ 2 * x + 2 * z ^ 3 = (x - z) ^ 2 * (x + 2 * z) := by
  ring

theorem one_atom_sparse_certificate_nonnegative (x z : ℝ)
    (hx : 0 ≤ x) (hz : 0 ≤ z) :
    0 ≤ x ^ 3 - 3 * z ^ 2 * x + 2 * z ^ 3 := by
  rw [one_atom_sparse_certificate]
  exact mul_nonneg (sq_nonneg (x - z)) (by linarith)

end ResearchCommons.ReactionPartialObservation
