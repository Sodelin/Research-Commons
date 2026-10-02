import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
namespace SyntheticCertificate
theorem expanded_cube (x y : ℚ) :
    (x+y)^3 = 1*x^3 + 3*x^2*y + 3*x*y^2 + 1*y^3 := by ring
theorem root_bracket (x : ℝ) (hx : 0 ≤ x) (hs : x^2 = 2) :
    (141421356 : ℝ)/100000000 < x ∧ x < (141421357 : ℝ)/100000000 := by
  constructor
  · by_contra h
    have hlt : x ≤ (141421356 : ℝ)/100000000 := le_of_not_gt h
    have hp : 0 ≤ (((141421356 : ℝ)/100000000)-x)*(((141421356 : ℝ)/100000000)+x) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  · by_contra h
    have hlt : (141421357 : ℝ)/100000000 ≤ x := le_of_not_gt h
    have hp : 0 ≤ (x-((141421357 : ℝ)/100000000))*(x+((141421357 : ℝ)/100000000)) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
#print axioms expanded_cube
#print axioms root_bracket
end SyntheticCertificate
