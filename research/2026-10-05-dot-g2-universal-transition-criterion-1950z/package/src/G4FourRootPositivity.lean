import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Arbitrary-interior-weight four-root forest defect certificate

Formal algebra contribution of the dedicated Lean lane. Source equations:
FOUR-ROOT-PLACEMENT.md, Commons 3d755ef391066069d33ff4490da65f00742b7ea7.
Original G4 derivation and ownership retained.

This certifies the explicit source-polynomial defect for one independent bigon.
Generator/forest interpretation, private-randomness composition/tomography and
full common-chain comparison are separate source bridges, not assumed axioms.
-/

namespace GProgram.G4.FourRoot

noncomputable def s2 (u x y : ℝ) : ℝ := u^2*x + (1-u)^2*y + 2*u*(1-u)
noncomputable def s3 (u x y : ℝ) : ℝ :=
  u^3*x^3 + (1-u)^3*y^3 + 3*u^2*(1-u)*x + 3*u*(1-u)^2*y
noncomputable def s4 (u x y : ℝ) : ℝ :=
  u^4*x^6 + (1-u)^4*y^6 + 4*u^3*(1-u)*x^3 +
    4*u*(1-u)^3*y^3 + 6*u^2*(1-u)^2*x*y
noncomputable def ordinaryOne4 (z : ℝ) : ℝ := 1 - 9*z/5 + z^3 - z^6/5
noncomputable def one4 (u x y : ℝ) : ℝ :=
  u^4*ordinaryOne4 x + (1-u)^4*ordinaryOne4 y
noncomputable def delta (u x y : ℝ) : ℝ :=
  one4 u x y - (1 - 9*(s2 u x y)/5 + s3 u x y - s4 u x y/5)
noncomputable def defect3 (u x y : ℝ) : ℝ := s3 u x y - (s2 u x y)^3
noncomputable def A (u x : ℝ) : ℝ := u*(1-x)
noncomputable def B (u y : ℝ) : ℝ := (1-u)*(1-y)

theorem exact_defect_factorization (u x y : ℝ) :
    defect3 u x y + 5*delta u x y =
      -u*(1-u)*(A u x-B u y)^2*((1+u)*A u x+(2-u)*B u y) := by
  unfold defect3 delta one4 ordinaryOne4 s2 s3 s4 A B
  ring

theorem defect3_in_barrier_coordinates (u x y : ℝ) :
    defect3 u x y = 3*u*(1-u)*(A u x-B u y)^2 -
      ((A u x)^3+(B u y)^3-(u*A u x+(1-u)*B u y)^3) := by
  unfold defect3 s2 s3 A B
  ring

/-- The exact zero-four-root-defect stratum has a strictly negative cubic
moment defect for every positive independent bigon, without genericity. -/
theorem zero_delta_forces_negative_defect3 {u x y : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hx1 : x < 1) (hy1 : y < 1)
    (hd : delta u x y = 0) : defect3 u x y < 0 := by
  have hv : 0 < 1-u := by linarith
  have ha : 0 < A u x := mul_pos hu (by linarith)
  have hb : 0 < B u y := mul_pos hv (by linarith)
  have hq : 0 < (1+u)*A u x+(2-u)*B u y :=
    add_pos (mul_pos (by linarith) ha) (mul_pos (by linarith) hb)
  by_cases he : A u x = B u y
  · have hmean : u*B u y+(1-u)*B u y = B u y := by ring
    have hh := defect3_in_barrier_coordinates u x y
    rw [he,hmean] at hh
    have hp := pow_pos hb 3
    nlinarith
  · have hsq : 0 < (A u x-B u y)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr he)
    have hp : 0 < u*(1-u)*(A u x-B u y)^2*((1+u)*A u x+(2-u)*B u y) :=
      mul_pos (mul_pos (mul_pos hu hv) hsq) hq
    have hh := exact_defect_factorization u x y
    rw [hd] at hh
    nlinarith

theorem no_common_moment_signature {u x y : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hx1 : x < 1) (hy1 : y < 1) :
    ¬ (delta u x y = 0 ∧ 0 ≤ defect3 u x y) := by
  rintro ⟨hd,hnonneg⟩
  exact not_lt_of_ge hnonneg (zero_delta_forces_negative_defect3 hu hu1 hx1 hy1 hd)

/-- Exact rational cap-three scalar witness used by the source's exchangeable
full-forest sharpness argument. That exchangeability bridge is not proved here. -/
theorem rational_cap3_scalar_witness :
    s2 (1/2) (37/42) (5/6) = 13/14 ∧
    s3 (1/2) (37/42) (5/6) = (13/14)^3 := by
  norm_num [s2,s3]

#print axioms exact_defect_factorization
#print axioms zero_delta_forces_negative_defect3
#print axioms no_common_moment_signature
#print axioms rational_cap3_scalar_witness

end GProgram.G4.FourRoot
