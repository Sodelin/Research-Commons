import G3BernoulliSmoothness

/-! Boundary regression examples for the factor-positive smoothness wrapper.
These test theorem applicability, not original-source realizability. -/

open scoped ContDiff

namespace GProgram.G3.AllResidue

example (n : ℕ) {k : ℕ∞ω} (q : ℝ) :
    ContDiffAt ℝ k
      (fun x : ℝ × ℝ => bernoulliLog n x.1 x.2) (0, q) := by
  apply contDiffAt_bernoulliLog_of_factor_pos
  simp [bernoulliFactor]

example (n : ℕ) {k : ℕ∞ω} (p : ℝ) :
    ContDiffAt ℝ k
      (fun x : ℝ × ℝ => bernoulliLog n x.1 x.2) (p, 1) := by
  apply contDiffAt_bernoulliLog_of_factor_pos
  simp [bernoulliFactor]

example (n : ℕ) (hn : n ≠ 0) {k : ℕ∞ω} {p : ℝ} (hp : p < 1) :
    ContDiffAt ℝ k
      (fun x : ℝ × ℝ => bernoulliLog n x.1 x.2) (p, 0) := by
  apply contDiffAt_bernoulliLog_of_factor_pos
  simpa only [bernoulliFactor, zero_pow hn, mul_zero, add_zero] using sub_pos.mpr hp

example {k : ℕ∞ω} (p q : ℝ) :
    ContDiffAt ℝ k
      (fun x : ℝ × ℝ => bernoulliLog 0 x.1 x.2) (p, q) := by
  apply contDiffAt_bernoulliLog_of_factor_pos
  simp [bernoulliFactor]

example (n : ℕ) (hn : n ≠ 0) :
    ¬ 0 < bernoulliFactor n 1 0 := by
  simp [bernoulliFactor, zero_pow hn]

end GProgram.G3.AllResidue
