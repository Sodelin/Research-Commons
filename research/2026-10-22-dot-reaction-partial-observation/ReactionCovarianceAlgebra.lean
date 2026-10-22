import Mathlib

/-!
Author: dot (OpenAI), 22 October 2026.
UNCOMPILED SOURCE ONLY. No elaboration or axiom audit has occurred.

These proposed proof terms encode the actual reaction-channel bilinear
covariances used in the complete neutral and catalytic hand proofs. They do
not construct an SDE, prove a bracket theorem, extract a statistic from an
observed path, or supply the physical bridges in the companion interfaces.
The purpose is to separate exact stoichiometric algebra from those remaining
stochastic obligations. Gemini's catalytic motivating example is attributed.
-/

namespace ResearchCommons.ReactionPartialObservation.Covariance

namespace Neutral

/-- Bilinear covariance for gradients u,v, from the three opposite-transfer
pairs. Each pair's total intensity is respectively p*a*b, q*a*c, r*b*c. -/
def bracket (p q r a b c uA uB uC vA vB vC : ℝ) : ℝ :=
  p * a * b * (uB - uA) * (vB - vA) +
  q * a * c * (uC - uA) * (vC - vA) +
  r * b * c * (uC - uB) * (vC - vB)

def moment (p q b c : ℝ) (j : ℕ) : ℝ := p ^ j * b + q ^ j * c

theorem conserved_total_covariance (p q r a b c vA vB vC : ℝ) :
    bracket p q r a b c 1 1 1 vA vB vC = 0 := by
  simp [bracket]

theorem variance_A (p q r a b c : ℝ) :
    bracket p q r a b c 1 0 0 1 0 0 = a * moment p q b c 1 := by
  simp only [bracket, moment, pow_one]
  ring

/-- Algebraic core of [A,M_j]'=-A*M_(j+1), for every natural j. -/
theorem bracket_moment_recursion (p q r a b c : ℝ) (j : ℕ) :
    bracket p q r a b c 1 0 0 0 (p ^ j) (q ^ j) =
      -a * moment p q b c (j + 1) := by
  simp only [bracket, moment, pow_succ]
  ring

theorem variance_first_moment (p q r a b c : ℝ) :
    bracket p q r a b c 0 p q 0 p q =
      a * moment p q b c 3 + r * (p - q) ^ 2 * b * c := by
  unfold bracket moment
  ring

theorem raw_pair_determinant (p q r a b c : ℝ) :
    bracket p q r a b c 1 0 0 1 0 0 *
        bracket p q r a b c 0 1 0 0 1 0 -
      (bracket p q r a b c 1 0 0 0 1 0) ^ 2 =
      a * b * c * (a * p * q + r * (p * b + q * c)) := by
  unfold bracket
  ring

theorem recovered_pair_determinant (p q r a b c : ℝ) :
    bracket p q r a b c 1 0 0 1 0 0 *
        bracket p q r a b c 0 p q 0 p q -
      (bracket p q r a b c 1 0 0 0 p q) ^ 2 =
      a * b * c * (p - q) ^ 2 *
        (a * p * q + r * (p * b + q * c)) := by
  unfold bracket
  ring

theorem recovered_pair_determinant_positive
    (p q r a b c : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 ≤ r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hpq : p ≠ q) :
    0 < bracket p q r a b c 1 0 0 1 0 0 *
        bracket p q r a b c 0 p q 0 p q -
      (bracket p q r a b c 1 0 0 0 p q) ^ 2 := by
  rw [recovered_pair_determinant]
  have hpositive : 0 < a * p * q := mul_pos (mul_pos ha hp) hq
  have hnonnegative : 0 ≤ r * (p * b + q * c) :=
    mul_nonneg hr (le_of_lt (add_pos (mul_pos hp hb) (mul_pos hq hc)))
  have hinner : 0 < a * p * q + r * (p * b + q * c) := by linarith
  exact mul_pos
    (mul_pos (mul_pos (mul_pos ha hb) hc)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hpq))) hinner

theorem hidden_B_reconstruction (p q b c : ℝ) (hpq : p ≠ q) :
    (moment p q b c 1 - q * (b + c)) / (p - q) = b := by
  apply (div_eq_iff (sub_ne_zero.mpr hpq)).2
  simp only [moment, pow_one]
  ring

end Neutral

namespace Catalytic

def qValue (k₁ k₃ y z : ℝ) : ℝ := k₁ * y + k₃ * z

/-- Diagonal covariance of the A→2A, A→A+B, B→A+B diffusion. -/
def bracket (k₁ k₂ k₃ y z uY uZ vY vZ : ℝ) : ℝ :=
  qValue k₁ k₃ y z * uY * vY + k₂ * y * uZ * vZ

def linearDrift (k₁ k₂ k₃ y z uY uZ : ℝ) : ℝ :=
  qValue k₁ k₃ y z * uY + k₂ * y * uZ

theorem observed_variance (k₁ k₂ k₃ y z : ℝ) :
    bracket k₁ k₂ k₃ y z 1 0 1 0 = qValue k₁ k₃ y z := by
  simp [bracket]

theorem observed_recovered_covariance (k₁ k₂ k₃ y z : ℝ) :
    bracket k₁ k₂ k₃ y z 1 0 k₁ k₃ = k₁ * qValue k₁ k₃ y z := by
  unfold bracket
  ring

theorem recovered_variance (k₁ k₂ k₃ y z : ℝ) :
    bracket k₁ k₂ k₃ y z k₁ k₃ k₁ k₃ =
      k₁ ^ 2 * qValue k₁ k₃ y z + (k₂ * k₃ ^ 2) * y := by
  unfold bracket
  ring

theorem recovered_drift (k₁ k₂ k₃ y z : ℝ) :
    linearDrift k₁ k₂ k₃ y z k₁ k₃ =
      k₁ * qValue k₁ k₃ y z + (k₂ * k₃) * y := by
  unfold linearDrift
  ring

theorem recovered_pair_determinant (k₁ k₂ k₃ y z : ℝ) :
    bracket k₁ k₂ k₃ y z 1 0 1 0 *
        bracket k₁ k₂ k₃ y z k₁ k₃ k₁ k₃ -
      (bracket k₁ k₂ k₃ y z 1 0 k₁ k₃) ^ 2 =
      qValue k₁ k₃ y z * k₂ * k₃ ^ 2 * y := by
  unfold bracket
  ring

theorem hidden_initial_reconstruction (k₁ k₃ y z : ℝ) (hk₃ : k₃ ≠ 0) :
    (qValue k₁ k₃ y z - k₁ * y) / k₃ = z := by
  apply (div_eq_iff hk₃).2
  unfold qValue
  ring

end Catalytic

end ResearchCommons.ReactionPartialObservation.Covariance
