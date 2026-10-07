import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
UNCHECKED candidate, 7 October 2026.

This formalizes only the finite scalar perturbation of the inherited G3
coupled-normal barrier. Uniform logarithmic factor estimates, the strict
COMMON source contract, the contrast lower bound and the finite Holder
count inequality remain separate hand/source obligations. There are no
source axioms or sorry placeholders. No Lean invocation has run here.
-/

namespace CloudG3.ApproximateMomentBarrier

theorem approximate_coupled_barrier
    {P Q T U d B0 B1 g K C ε : ℝ}
    (hP : 0 ≤ P) (hT : 0 ≤ T) (hd : 0 < d)
    (hB1 : 0 ≤ B1)
    (hPQ : d * P ≤ B0 * Q + ε)
    (hTP : g * T ≤ ε + B1 * P ^ 2)
    (hQT : Q ^ 2 ≤ U * T) (hUC : U ≤ K * C)
    (hgap : 2 * B1 * B0 ^ 2 * K * C ≤ d ^ 2 * g / 2) :
    d ^ 2 * g * T / 2 ≤ d ^ 2 * ε + 2 * B1 * ε ^ 2 := by
  have hleft : 0 ≤ d * P := mul_nonneg hd.le hP
  have hsq0 := mul_self_le_mul_self hleft hPQ
  have hsq : d ^ 2 * P ^ 2 ≤ 2 * B0 ^ 2 * Q ^ 2 + 2 * ε ^ 2 := by
    nlinarith only [hsq0, sq_nonneg (B0 * Q - ε)]
  have h1 : d ^ 2 * g * T ≤ d ^ 2 * ε + d ^ 2 * B1 * P ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hTP (sq_nonneg d)
    nlinarith only [hh]
  have h2 : d ^ 2 * B1 * P ^ 2 ≤
      2 * B1 * B0 ^ 2 * Q ^ 2 + 2 * B1 * ε ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsq hB1
    nlinarith only [hh]
  have hcoefficient : 0 ≤ 2 * B1 * B0 ^ 2 := by positivity
  have h3 : 2 * B1 * B0 ^ 2 * Q ^ 2 ≤
      2 * B1 * B0 ^ 2 * U * T := by
    have hh := mul_le_mul_of_nonneg_left hQT hcoefficient
    nlinarith only [hh]
  have h4 : 2 * B1 * B0 ^ 2 * U * T ≤
      2 * B1 * B0 ^ 2 * K * C * T := by
    have hh := mul_le_mul_of_nonneg_left hUC (mul_nonneg hcoefficient hT)
    nlinarith only [hh]
  have h5 : 2 * B1 * B0 ^ 2 * K * C * T ≤ d ^ 2 * g * T / 2 := by
    have hh := mul_le_mul_of_nonneg_right hgap hT
    nlinarith only [hh]
  linarith

#print axioms approximate_coupled_barrier

end CloudG3.ApproximateMomentBarrier
