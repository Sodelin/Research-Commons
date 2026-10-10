import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Exact real positivity obligations from the executed cap-seven all-r
critical-locus packet. No resultant, finiteness or source theorem is assumed. -/
namespace GProgram.G3.AllResidue

def exceptionalJ (r : ℝ) : ℝ :=
  r^34 + r^33 + (-1 : ℝ)*r^32 + (9 : ℝ)*r^31 + (5 : ℝ)*r^29 + (26 : ℝ)*r^28 + (6 : ℝ)*r^27 + (19 : ℝ)*r^26 + (64 : ℝ)*r^25 + (6 : ℝ)*r^24 + (66 : ℝ)*r^23 + (79 : ℝ)*r^22 + (29 : ℝ)*r^21 + (105 : ℝ)*r^20 + (84 : ℝ)*r^19 + (45 : ℝ)*r^18 + (137 : ℝ)*r^17 + (45 : ℝ)*r^16 + (84 : ℝ)*r^15 + (105 : ℝ)*r^14 + (29 : ℝ)*r^13 + (79 : ℝ)*r^12 + (66 : ℝ)*r^11 + (6 : ℝ)*r^10 + (64 : ℝ)*r^9 + (19 : ℝ)*r^8 + (6 : ℝ)*r^7 + (26 : ℝ)*r^6 + (5 : ℝ)*r^5 + (9 : ℝ)*r^3 + (-1 : ℝ)*r^2 + r + (1 : ℝ)

def exceptionalRemainder (r : ℝ) : ℝ :=
  (5 : ℝ)*r^29 + (26 : ℝ)*r^28 + (6 : ℝ)*r^27 + (19 : ℝ)*r^26 + (64 : ℝ)*r^25 + (6 : ℝ)*r^24 + (66 : ℝ)*r^23 + (79 : ℝ)*r^22 + (29 : ℝ)*r^21 + (105 : ℝ)*r^20 + (84 : ℝ)*r^19 + (45 : ℝ)*r^18 + (137 : ℝ)*r^17 + (45 : ℝ)*r^16 + (84 : ℝ)*r^15 + (105 : ℝ)*r^14 + (29 : ℝ)*r^13 + (79 : ℝ)*r^12 + (66 : ℝ)*r^11 + (6 : ℝ)*r^10 + (64 : ℝ)*r^9 + (19 : ℝ)*r^8 + (6 : ℝ)*r^7 + (26 : ℝ)*r^6 + (5 : ℝ)*r^5

theorem quadratic_factor_pos (r : ℝ) : 0 < r^2-r+1 := by
  nlinarith [sq_nonneg (r-(1/2 : ℝ))]

theorem exceptionalJ_exact (r : ℝ) :
    exceptionalJ r =
      r^31 * (r^3 + (r-(1/2 : ℝ))^2 + 35/4) +
      r * (9*(r-(1/18 : ℝ))^2 + 35/36) + 1 + exceptionalRemainder r := by
  unfold exceptionalJ exceptionalRemainder
  ring

theorem exceptional_remainder_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ exceptionalRemainder r := by
  unfold exceptionalRemainder
  positivity

theorem exceptionalJ_pos {r : ℝ} (hr : 0 < r) : 0 < exceptionalJ r := by
  rw [exceptionalJ_exact]
  have hrem := exceptional_remainder_nonneg hr
  positivity

def factor0 (r : ℝ) : ℝ := r
theorem factor0_pos {r : ℝ} (hr : 0 < r) : 0 < factor0 r := by
  unfold factor0
  positivity

def factor1 (r : ℝ) : ℝ := r^2 + (-1 : ℝ)*r + (1 : ℝ)
theorem factor1_pos {r : ℝ} (hr : 0 < r) : 0 < factor1 r := by
  unfold factor1
  nlinarith [quadratic_factor_pos r]

def factor2 (r : ℝ) : ℝ := r^2 + r + (1 : ℝ)
theorem factor2_pos {r : ℝ} (hr : 0 < r) : 0 < factor2 r := by
  unfold factor2
  positivity

def factor3 (r : ℝ) : ℝ := r^4 + r^3 + r^2 + r + (1 : ℝ)
theorem factor3_pos {r : ℝ} (hr : 0 < r) : 0 < factor3 r := by
  unfold factor3
  positivity

def factor4 (r : ℝ) : ℝ := (5 : ℝ)*r^20 + (15 : ℝ)*r^19 + (25 : ℝ)*r^18 + (75 : ℝ)*r^17 + (94 : ℝ)*r^16 + (167 : ℝ)*r^15 + (246 : ℝ)*r^14 + (278 : ℝ)*r^13 + (347 : ℝ)*r^12 + (410 : ℝ)*r^11 + (351 : ℝ)*r^10 + (410 : ℝ)*r^9 + (347 : ℝ)*r^8 + (278 : ℝ)*r^7 + (246 : ℝ)*r^6 + (167 : ℝ)*r^5 + (94 : ℝ)*r^4 + (75 : ℝ)*r^3 + (25 : ℝ)*r^2 + (15 : ℝ)*r + (5 : ℝ)
theorem factor4_pos {r : ℝ} (hr : 0 < r) : 0 < factor4 r := by
  unfold factor4
  positivity

def factor5 (r : ℝ) : ℝ := (8 : ℝ)*r^30 + (8 : ℝ)*r^29 + (32 : ℝ)*r^28 + (52 : ℝ)*r^27 + (100 : ℝ)*r^26 + (135 : ℝ)*r^25 + (243 : ℝ)*r^24 + (308 : ℝ)*r^23 + (422 : ℝ)*r^22 + (557 : ℝ)*r^21 + (690 : ℝ)*r^20 + (735 : ℝ)*r^19 + (958 : ℝ)*r^18 + (943 : ℝ)*r^17 + (1002 : ℝ)*r^16 + (1089 : ℝ)*r^15 + (1002 : ℝ)*r^14 + (943 : ℝ)*r^13 + (958 : ℝ)*r^12 + (735 : ℝ)*r^11 + (690 : ℝ)*r^10 + (557 : ℝ)*r^9 + (422 : ℝ)*r^8 + (308 : ℝ)*r^7 + (243 : ℝ)*r^6 + (135 : ℝ)*r^5 + (100 : ℝ)*r^4 + (52 : ℝ)*r^3 + (32 : ℝ)*r^2 + (8 : ℝ)*r + (8 : ℝ)
theorem factor5_pos {r : ℝ} (hr : 0 < r) : 0 < factor5 r := by
  unfold factor5
  positivity

def factor6 (r : ℝ) : ℝ := (11 : ℝ)*r^32 + (33 : ℝ)*r^31 + (55 : ℝ)*r^30 + (165 : ℝ)*r^29 + (218 : ℝ)*r^28 + (401 : ℝ)*r^27 + (610 : ℝ)*r^26 + (794 : ℝ)*r^25 + (1077 : ℝ)*r^24 + (1430 : ℝ)*r^23 + (1585 : ℝ)*r^22 + (2062 : ℝ)*r^21 + (2244 : ℝ)*r^20 + (2515 : ℝ)*r^19 + (2720 : ℝ)*r^18 + (2875 : ℝ)*r^17 + (2835 : ℝ)*r^16 + (2875 : ℝ)*r^15 + (2720 : ℝ)*r^14 + (2515 : ℝ)*r^13 + (2244 : ℝ)*r^12 + (2062 : ℝ)*r^11 + (1585 : ℝ)*r^10 + (1430 : ℝ)*r^9 + (1077 : ℝ)*r^8 + (794 : ℝ)*r^7 + (610 : ℝ)*r^6 + (401 : ℝ)*r^5 + (218 : ℝ)*r^4 + (165 : ℝ)*r^3 + (55 : ℝ)*r^2 + (33 : ℝ)*r + (11 : ℝ)
theorem factor6_pos {r : ℝ} (hr : 0 < r) : 0 < factor6 r := by
  unfold factor6
  positivity

def factor7 (r : ℝ) : ℝ := exceptionalJ r
theorem factor7_pos {r : ℝ} (hr : 0 < r) : 0 < factor7 r := by
  exact exceptionalJ_pos hr

def factor8 (r : ℝ) : ℝ := (8 : ℝ)*r^34 + (8 : ℝ)*r^33 + (40 : ℝ)*r^32 + (72 : ℝ)*r^31 + (152 : ℝ)*r^30 + (163 : ℝ)*r^29 + (503 : ℝ)*r^28 + (355 : ℝ)*r^27 + (887 : ℝ)*r^26 + (1042 : ℝ)*r^25 + (1243 : ℝ)*r^24 + (1643 : ℝ)*r^23 + (2315 : ℝ)*r^22 + (1682 : ℝ)*r^21 + (3187 : ℝ)*r^20 + (2530 : ℝ)*r^19 + (2690 : ℝ)*r^18 + (3385 : ℝ)*r^17 + (2690 : ℝ)*r^16 + (2530 : ℝ)*r^15 + (3187 : ℝ)*r^14 + (1682 : ℝ)*r^13 + (2315 : ℝ)*r^12 + (1643 : ℝ)*r^11 + (1243 : ℝ)*r^10 + (1042 : ℝ)*r^9 + (887 : ℝ)*r^8 + (355 : ℝ)*r^7 + (503 : ℝ)*r^6 + (163 : ℝ)*r^5 + (152 : ℝ)*r^4 + (72 : ℝ)*r^3 + (40 : ℝ)*r^2 + (8 : ℝ)*r + (8 : ℝ)
theorem factor8_pos {r : ℝ} (hr : 0 < r) : 0 < factor8 r := by
  unfold factor8
  positivity

def factor9 (r : ℝ) : ℝ := (7 : ℝ)*r^40 + (28 : ℝ)*r^39 + (64 : ℝ)*r^38 + (157 : ℝ)*r^37 + (310 : ℝ)*r^36 + (553 : ℝ)*r^35 + (933 : ℝ)*r^34 + (1505 : ℝ)*r^33 + (2217 : ℝ)*r^32 + (3252 : ℝ)*r^31 + (4490 : ℝ)*r^30 + (5973 : ℝ)*r^29 + (7718 : ℝ)*r^28 + (9670 : ℝ)*r^27 + (11567 : ℝ)*r^26 + (13672 : ℝ)*r^25 + (15465 : ℝ)*r^24 + (17018 : ℝ)*r^23 + (18246 : ℝ)*r^22 + (19047 : ℝ)*r^21 + (19191 : ℝ)*r^20 + (19047 : ℝ)*r^19 + (18246 : ℝ)*r^18 + (17018 : ℝ)*r^17 + (15465 : ℝ)*r^16 + (13672 : ℝ)*r^15 + (11567 : ℝ)*r^14 + (9670 : ℝ)*r^13 + (7718 : ℝ)*r^12 + (5973 : ℝ)*r^11 + (4490 : ℝ)*r^10 + (3252 : ℝ)*r^9 + (2217 : ℝ)*r^8 + (1505 : ℝ)*r^7 + (933 : ℝ)*r^6 + (553 : ℝ)*r^5 + (310 : ℝ)*r^4 + (157 : ℝ)*r^3 + (64 : ℝ)*r^2 + (28 : ℝ)*r + (7 : ℝ)
theorem factor9_pos {r : ℝ} (hr : 0 < r) : 0 < factor9 r := by
  unfold factor9
  positivity

def criticalGcdProduct (r : ℝ) : ℝ :=
  (factor0 r)^22 * (factor1 r)^3 * (factor2 r)^6 * (factor3 r)^2 * (factor4 r)^1 * (factor5 r)^1 * (factor6 r)^1 * (factor7 r)^1 * (factor8 r)^1 * (factor9 r)^1

theorem critical_gcd_product_pos {r : ℝ} (hr : 0 < r) :
    0 < criticalGcdProduct r := by
  have h_factor0 := factor0_pos hr
  have h_factor1 := factor1_pos hr
  have h_factor2 := factor2_pos hr
  have h_factor3 := factor3_pos hr
  have h_factor4 := factor4_pos hr
  have h_factor5 := factor5_pos hr
  have h_factor6 := factor6_pos hr
  have h_factor7 := factor7_pos hr
  have h_factor8 := factor8_pos hr
  have h_factor9 := factor9_pos hr
  unfold criticalGcdProduct
  positivity

#print axioms quadratic_factor_pos
#print axioms exceptionalJ_exact
#print axioms exceptional_remainder_nonneg
#print axioms exceptionalJ_pos
#print axioms critical_gcd_product_pos

end GProgram.G3.AllResidue
