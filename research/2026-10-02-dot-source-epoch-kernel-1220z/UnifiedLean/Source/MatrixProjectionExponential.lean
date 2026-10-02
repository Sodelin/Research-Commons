import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Rectangular projection through finite matrix exponentials

Contributor: GPT-6.1 Sol / continue_g_research, 2026-10-02.
This conditional linear-algebra adapter reuses mathlib's exponential series,
`SemiconjBy.exp_right`, and finite block-matrix algebra. It is for the actual
finite-source integration lead's generator/projection instance; no source law,
stochasticity, hidden graph budget or observed-process equivalence is assumed
proved merely by constructing these matrices. No novelty of this standard
matrix principle is claimed. Frozen100 is unchanged; this is next-version work.
-/
namespace UnifiedLean.Source.MatrixProjectionExponential
open Matrix NormedSpace
open scoped Matrix.Norms.Operator
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The ordinary block-diagonal additive map; no fitted stochastic kernel. -/
def diagonalPairHom : (Matrix m m ℝ × Matrix n n ℝ) →+
    Matrix (m ⊕ n) (m ⊕ n) ℝ where
  toFun p := fromBlocks p.1 0 0 p.2
  map_zero' := fromBlocks_zero
  map_add' p q := by simp [fromBlocks_add]

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
lemma diagonalPairHom_continuous : Continuous
    (diagonalPairHom : (Matrix m m ℝ × Matrix n n ℝ) →
      Matrix (m ⊕ n) (m ⊕ n) ℝ) :=
  continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd

/-- Unequal finite block sizes are allowed. The inherited power identity and
continuous additive pushforward of the convergent exponential series suffice. -/
theorem exp_fromBlocks_diagonal (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    exp (fromBlocks A 0 0 B) = fromBlocks (exp A) 0 0 (exp B) := by
  have hA := exp_series_hasSum_exp' (𝕂 := ℚ) A
  have hB := exp_series_hasSum_exp' (𝕂 := ℚ) B
  have hs := (hA.prodMk hB).map diagonalPairHom diagonalPairHom_continuous
  change HasSum (fun k : ℕ => fromBlocks ((k.factorial⁻¹ : ℚ) • A ^ k) 0 0
    ((k.factorial⁻¹ : ℚ) • B ^ k)) (fromBlocks (exp A) 0 0 (exp B)) at hs
  have ht : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℚ) • (fromBlocks A 0 0 B) ^ k)
      (fromBlocks (exp A) 0 0 (exp B)) := by
    simpa only [fromBlocks_diagonal_pow, fromBlocks_smul, smul_zero] using hs
  rw [exp_eq_tsum_rat]
  exact ht.tsum_eq

/-- Actual rectangular generator identity transports through the exponential.
The identity A*P=P*B is an explicit hypothesis that source integration must
PROVE from the admitted original-source generator and its chosen projection. -/
theorem rectangular_exp_intertwining (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (P : Matrix m n ℝ) (h : A * P = P * B) :
    exp A * P = P * exp B := by
  let C : Matrix (m ⊕ n) (m ⊕ n) ℝ := fromBlocks 0 P 0 0
  let D : Matrix (m ⊕ n) (m ⊕ n) ℝ := fromBlocks A 0 0 B
  have hd : SemiconjBy C D D := by
    change C * D = D * C
    simp only [C, D, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
    rw [h]
  have he := hd.exp_right
  change C * exp D = exp D * C at he
  rw [show exp D = fromBlocks (exp A) 0 0 (exp B) from exp_fromBlocks_diagonal A B] at he
  have hp := congrArg Matrix.toBlocks₁₂ he
  simpa only [C, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
    toBlocks_fromBlocks₁₂] using hp.symm

/-- Arbitrary real duration; nonnegative durations/stochastic generators are
additional source hypotheses, not needed by this algebraic implication. -/
theorem rectangular_scaled_exp_intertwining (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (P : Matrix m n ℝ) (h : A * P = P * B) (t : ℝ) :
    exp (t • A) * P = P * exp (t • B) := by
  apply rectangular_exp_intertwining
  rw [Matrix.smul_mul, Matrix.mul_smul, h]

omit [DecidableEq m] [DecidableEq n] in
/-- Two already established pulse/interval kernel identities compose in order.
This does not itself establish any natural biological pulse identity. -/
theorem rectangular_product_intertwining
    (A₁ A₂ : Matrix m m ℝ) (B₁ B₂ : Matrix n n ℝ) (P : Matrix m n ℝ)
    (h₁ : A₁ * P = P * B₁) (h₂ : A₂ * P = P * B₂) :
    (A₁ * A₂) * P = P * (B₁ * B₂) := by
  rw [Matrix.mul_assoc, h₂, ← Matrix.mul_assoc, h₁, Matrix.mul_assoc]

#print axioms exp_fromBlocks_diagonal
#print axioms rectangular_exp_intertwining
#print axioms rectangular_scaled_exp_intertwining
#print axioms rectangular_product_intertwining
end UnifiedLean.Source.MatrixProjectionExponential
