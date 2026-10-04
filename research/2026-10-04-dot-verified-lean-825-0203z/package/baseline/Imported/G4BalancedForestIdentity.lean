import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Fair independent-bigon cap-four balanced-forest identity

New formal algebra/check contribution: dot's dedicated Lean lane, 2026-10-01.
The source setting is one independent bigon at g=1/2, with fixed arm survivals
x,y for every input size. The four original input tokens are labelled. The
balanced coordinate is the unranked output forest {AB,CD}, with no later merge.

The concrete probability-polynomial/source-generator interpretation is subject
to the separate source review. No full source-to-law implication, arbitrary g,
arbitrary chain cutoff, or complete G4 closure is assumed or claimed here.
-/

namespace GProgram.G4

noncomputable def bigonNoMerger2 (x y : ℝ) : ℝ := (x + y + 2) / 4
noncomputable def bigonNoMerger3 (x y : ℝ) : ℝ := (x^3 + y^3 + 3*x + 3*y) / 8
noncomputable def bigonNoMerger4 (x y : ℝ) : ℝ :=
  (x^6 + y^6 + 4*x^3 + 4*y^3 + 6*x*y) / 16

/-- One fixed balanced labelled forest on a positive ordinary population edge.
Two possible pair-merge orders give the same unranked output forest. -/
noncomputable def ordinaryBalanced4 (z : ℝ) : ℝ := z / 5 - z^3 / 3 + 2*z^6 / 15

/-- All four tokens on one parent, or the two named pairs on separate parents. -/
noncomputable def bigonBalanced4 (x y : ℝ) : ℝ :=
  (ordinaryBalanced4 x + ordinaryBalanced4 y) / 16 + (1-x)*(1-y)/8

theorem ordinary_balanced_factorization (z : ℝ) :
    ordinaryBalanced4 z = z * (1-z)^2 * (2*z^3+4*z^2+6*z+3) / 15 := by
  unfold ordinaryBalanced4
  ring

theorem ordinary_balanced_positive {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    0 < ordinaryBalanced4 z := by
  rw [ordinary_balanced_factorization]
  have h1 : 0 < (1-z)^2 := pow_pos (by linarith) 2
  have h2 : 0 < 2*z^3+4*z^2+6*z+3 := by positivity
  positivity

/-- Exact cleared-denominator residual identity. No numerical approximations
or hidden nonlinear solving are used. -/
theorem balanced_residual_identity (x y : ℝ) :
    640*(x+y)*(bigonBalanced4 x y - ordinaryBalanced4 (bigonNoMerger2 x y)) +
      (x+y-2)^4 =
    (256/3)*(x+y)*(bigonNoMerger4 x y - (bigonNoMerger2 x y)^6) -
      ((832/3)*(x+y)+128)*(bigonNoMerger3 x y - (bigonNoMerger2 x y)^3) := by
  unfold bigonBalanced4 ordinaryBalanced4 bigonNoMerger2 bigonNoMerger3 bigonNoMerger4
  ring

/-- A fair positive bigon's cap-four full-forest coordinates cannot all equal
those of its pair-calibrated ordinary edge, even when no-merger coordinates do. -/
theorem balanced_coordinate_separates_cap4 {x y : ℝ} (hx1 : x < 1) (hy1 : y < 1) :
    ¬ (bigonNoMerger3 x y = (bigonNoMerger2 x y)^3 ∧
       bigonNoMerger4 x y = (bigonNoMerger2 x y)^6 ∧
       bigonBalanced4 x y = ordinaryBalanced4 (bigonNoMerger2 x y)) := by
  rintro ⟨h3,h4,hpair⟩
  have h := balanced_residual_identity x y
  rw [h3,h4,hpair] at h
  have hp : 0 < (2-(x+y))^4 := pow_pos (by linarith) 4
  have he : (2-(x+y))^4 = (x+y-2)^4 := by ring
  rw [he] at hp
  nlinarith

#print axioms balanced_residual_identity
#print axioms balanced_coordinate_separates_cap4
#print axioms ordinary_balanced_positive

end GProgram.G4
