import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace G4CountUniform

/-- The two within-pair coin coefficient rows span the two universal
odd-jet generators, conditional on their stated coefficient representation. -/
theorem paired_odd_coefficient_determinant (a P epsilon : ℝ)
    (ha : 0 < a) (hP : 0 < P) (hepsilon : 0 ≤ epsilon) :
    P^3 * ((epsilon^3+a)*P^3/48) -
      (epsilon*P)^3 * ((1-a)*P^3/48) =
        a*P^6*(1+epsilon^3)/48 ∧
    0 < P^3 * ((epsilon^3+a)*P^3/48) -
      (epsilon*P)^3 * ((1-a)*P^3/48) := by
  have hid : P^3 * ((epsilon^3+a)*P^3/48) -
      (epsilon*P)^3 * ((1-a)*P^3/48) = a*P^6*(1+epsilon^3)/48 := by ring
  refine ⟨hid, ?_⟩
  rw [hid]
  positivity

end G4CountUniform
