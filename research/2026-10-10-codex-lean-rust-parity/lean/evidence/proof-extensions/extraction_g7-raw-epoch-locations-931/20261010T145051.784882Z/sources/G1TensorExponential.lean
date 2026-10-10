import UnifiedLean.Source.MatrixProjectionExponential
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Standard finite tensor-sum exponential algebra. Contributor: dot,
2026-10-03. This module claims no source-instance admission on its own. -/
namespace G1TensorExponential
set_option backward.isDefEq.respectTransparency false
open Matrix NormedSpace
open scoped Classical Kronecker Matrix.Norms.Operator
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def leftTensorHom : Matrix A A ℝ →+ Matrix (A × B) (A × B) ℝ where
  toFun M := M ⊗ₖ (1 : Matrix B B ℝ)
  map_zero' := zero_kronecker _
  map_add' M N := add_kronecker M N _

def rightTensorHom : Matrix B B ℝ →+ Matrix (A × B) (A × B) ℝ where
  toFun M := (1 : Matrix A A ℝ) ⊗ₖ M
  map_zero' := kronecker_zero _
  map_add' M N := kronecker_add _ M N

lemma leftTensorHom_continuous : Continuous (leftTensorHom : Matrix A A ℝ → Matrix (A × B) (A × B) ℝ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun M : Matrix A A ℝ => M i.1 j.1 * (1 : Matrix B B ℝ) i.2 j.2)
  fun_prop

lemma rightTensorHom_continuous : Continuous (rightTensorHom : Matrix B B ℝ → Matrix (A × B) (A × B) ℝ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun M : Matrix B B ℝ => (1 : Matrix A A ℝ) i.1 j.1 * M i.2 j.2)
  fun_prop

lemma left_tensor_pow (M : Matrix A A ℝ) (n : Nat) :
    (M ⊗ₖ (1 : Matrix B B ℝ)) ^ n = (M ^ n) ⊗ₖ (1 : Matrix B B ℝ) := by
  induction n with
  | zero => simp only [pow_zero,one_kronecker_one]
  | succ n ih => rw [pow_succ,ih,← mul_kronecker_mul,Matrix.one_mul,← pow_succ]

lemma right_tensor_pow (M : Matrix B B ℝ) (n : Nat) :
    ((1 : Matrix A A ℝ) ⊗ₖ M) ^ n = (1 : Matrix A A ℝ) ⊗ₖ (M ^ n) := by
  induction n with
  | zero => simp only [pow_zero,one_kronecker_one]
  | succ n ih => rw [pow_succ,ih,← mul_kronecker_mul,Matrix.one_mul,← pow_succ]

theorem exp_left_tensor (M : Matrix A A ℝ) :
    exp (M ⊗ₖ (1 : Matrix B B ℝ)) = exp M ⊗ₖ (1 : Matrix B B ℝ) := by
  have hs := (exp_series_hasSum_exp' (𝕂 := ℝ) M).map (leftTensorHom (A := A) (B := B)) leftTensorHom_continuous
  change HasSum (fun k : Nat => ((k.factorial : ℝ)⁻¹ • M ^ k) ⊗ₖ (1 : Matrix B B ℝ))
    (exp M ⊗ₖ (1 : Matrix B B ℝ)) at hs
  have ht : HasSum (fun k : Nat => (k.factorial : ℝ)⁻¹ • (M ⊗ₖ (1 : Matrix B B ℝ)) ^ k)
    (exp M ⊗ₖ (1 : Matrix B B ℝ)) := by
    simpa only [left_tensor_pow,smul_kronecker] using hs
  exact (exp_series_hasSum_exp' (𝕂 := ℝ) (M ⊗ₖ (1 : Matrix B B ℝ))).unique ht

theorem exp_right_tensor (M : Matrix B B ℝ) :
    exp ((1 : Matrix A A ℝ) ⊗ₖ M) = (1 : Matrix A A ℝ) ⊗ₖ exp M := by
  have hs := (exp_series_hasSum_exp' (𝕂 := ℝ) M).map (rightTensorHom (A := A) (B := B)) rightTensorHom_continuous
  change HasSum (fun k : Nat => (1 : Matrix A A ℝ) ⊗ₖ ((k.factorial : ℝ)⁻¹ • M ^ k))
    ((1 : Matrix A A ℝ) ⊗ₖ exp M) at hs
  have ht : HasSum (fun k : Nat => (k.factorial : ℝ)⁻¹ • ((1 : Matrix A A ℝ) ⊗ₖ M) ^ k)
    ((1 : Matrix A A ℝ) ⊗ₖ exp M) := by
    simpa only [right_tensor_pow,kronecker_smul] using hs
  exact (exp_series_hasSum_exp' (𝕂 := ℝ) ((1 : Matrix A A ℝ) ⊗ₖ M)).unique ht

/-- Independent generators commute in the product state carrier. -/
theorem exp_tensor_sum (M : Matrix A A ℝ) (N : Matrix B B ℝ) :
    exp (M ⊗ₖ (1 : Matrix B B ℝ) + (1 : Matrix A A ℝ) ⊗ₖ N) = exp M ⊗ₖ exp N := by
  have hc : Commute (M ⊗ₖ (1 : Matrix B B ℝ)) ((1 : Matrix A A ℝ) ⊗ₖ N) := by
    change _ * _ = _ * _
    rw [← mul_kronecker_mul,← mul_kronecker_mul]
    simp only [Matrix.mul_one,Matrix.one_mul]
  rw [exp_add_of_commute hc,exp_left_tensor,exp_right_tensor,← mul_kronecker_mul]
  simp only [Matrix.mul_one,Matrix.one_mul]

#print axioms exp_tensor_sum
end G1TensorExponential
