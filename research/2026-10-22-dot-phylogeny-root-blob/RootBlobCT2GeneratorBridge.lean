import RootBlobCT2RetainedImage
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit positive-rate K2P generator bridge

Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No compiler/runtime/kernel pass is claimed.

Pinned primary APIs (mathlib 0df444a360eaa60ab8c11dca51a86af692955474):
MatrixExponential.lean: exp_diagonal, exp_units_conj;
Normed/Algebra/Exponential.lean: Pi.exp_def;
SpecialFunctions/Exponential.lean: Real.exp_eq_exp_ℝ;
SpecialFunctions/Log/Basic.lean: log_lt_log, log_pow, log_neg, exp_log.

The matrix is the exponential of the actual Klein-four K2P generator,
not a merely positive stochastic matrix. Rate a is the g3 jump; both g1/g2
jumps have rate b. Each edge has independent a,b>0, with time absorbed into
the rates. Uniform root and original inheritance remain unchanged.
-/

open scoped BigOperators Matrix
open RootBlobInterfaces RootBlobKleinFourAlgebra RootBlobCT2RetainedImage
namespace RootBlobCT2GeneratorBridge

def k2Increment (x y : ℝ) (z : DNA) : ℝ :=
  if z = 0 then (1 + 2 * x + y) / 4
  else if z = g3 then (1 - 2 * x + y) / 4 else (1 - y) / 4

def k2Kernel (x y : ℝ) : Mat DNA := kernel (k2Increment x y)

theorem k2_fourier (x y : ℝ) (g : DNA) :
    fourier (k2Increment x y) g = if g = 0 then 1 else if g = g3 then y else x := by
  rcases dna_cases g with rfl | rfl | rfl | rfl
  all_goals simp only [fourier, sum_four]
  all_goals norm_num [k2Increment, character, g1, g2, g3]
  all_goals ring

theorem k2_eigen (x y : ℝ) (g : DNA) :
    eigen (k2Kernel x y) g = if g = 0 then 1 else if g = g3 then y else x := by
  simpa [eigen, k2Kernel, kernel] using k2_fourier x y g

theorem k2Kernel_ct2 {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (hxy : x^2 < y) : CT2Strict (k2Kernel x y) := by
  have hp : Probability (k2Increment x y) := by
    constructor
    · intro z
      unfold k2Increment
      split_ifs
      · linarith
      · nlinarith [sq_nonneg (1 - x)]
      · linarith
    · rw [sum_four]
      norm_num [k2Increment, g1, g2, g3]
      ring
  refine ⟨⟨k2Increment x y, hp, fun _ _ => rfl, ?_, ?_⟩, ?_⟩
  · intro g hg
    rw [k2_fourier, if_neg hg]
    split_ifs
    · exact ⟨hy0, hy1⟩
    · exact ⟨hx0, hx1⟩
  · rw [k2_fourier, k2_fourier]
    norm_num [g3]
  · simpa [k2_eigen, g3] using hxy

theorem nucleotide_k2_reconstruct {M : Mat DNA} (hM : NucleotideTransition .k2p M) :
    M = k2Kernel (eigen M g1) (eigen M g3) := by
  rcases hM with ⟨p, hp, hform, hλ, hmodel⟩
  have he : fourier p g1 = fourier p g2 := hmodel
  have ht := hp.2
  rw [sum_four] at ht
  have hp0 := fourier_inverse_zero p hp.2
  have h1 := fourier_g1 p
  have h2 := fourier_g2 p
  have h3 := fourier_g3 p
  have hcoord : ∀ z, p z = k2Increment (fourier p g1) (fourier p g3) z := by
    intro z
    rcases dna_cases z with rfl | rfl | rfl | rfl
    all_goals norm_num [k2Increment, g1, g2, g3] at *
    all_goals linarith
  funext i j
  simp only [k2Kernel, kernel, eigen, hform, sub_zero]
  exact hcoord (j - i)

def generatorIncrement (a b : ℝ) (z : DNA) : ℝ :=
  if z = 0 then -(a + 2 * b) else if z = g3 then a else b

def generator (a b : ℝ) : Matrix DNA DNA ℝ := kernel (generatorIncrement a b)

theorem generator_rows_zero (a b : ℝ) (i : DNA) :
    (∑ j, generator a b i j) = 0 := by
  change (∑ j, generatorIncrement a b (j - i)) = 0
  rw [shifted_sum, sum_four]
  norm_num [generatorIncrement, g1, g2, g3]
  ring

theorem generator_off_diagonal {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (i j : DNA) (hij : i ≠ j) : 0 < generator a b i j := by
  have hn : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
  simp only [generator, kernel, generatorIncrement, if_neg hn]
  split_ifs <;> assumption

def generatorSpectrum (a b : ℝ) (g : DNA) : ℝ :=
  if g = 0 then 0 else if g = g3 then -4 * b else -2 * (a + b)

def hadamard : Matrix DNA DNA ℝ := fun i g => character g i
def hadamardInverse : Matrix DNA DNA ℝ := fun g i => character g i / 4

theorem hadamard_mul_inverse : hadamard * hadamardInverse = 1 := by
  ext i j
  rcases dna_cases i with rfl | rfl | rfl | rfl <;>
    rcases dna_cases j with rfl | rfl | rfl | rfl
  all_goals simp only [Matrix.mul_apply, sum_four]
  all_goals norm_num [hadamard, hadamardInverse, character, Matrix.one_apply, g1, g2, g3]

theorem hadamard_inverse_mul : hadamardInverse * hadamard = 1 := by
  ext i j
  rcases dna_cases i with rfl | rfl | rfl | rfl <;>
    rcases dna_cases j with rfl | rfl | rfl | rfl
  all_goals simp only [Matrix.mul_apply, sum_four]
  all_goals norm_num [hadamard, hadamardInverse, character, Matrix.one_apply, g1, g2, g3]

def hadamardUnit : (Matrix DNA DNA ℝ)ˣ where
  val := hadamard
  inv := hadamardInverse
  val_inv := hadamard_mul_inverse
  inv_val := hadamard_inverse_mul

theorem generator_diagonalization (a b : ℝ) :
    generator a b = hadamard * Matrix.diagonal (generatorSpectrum a b) * hadamardInverse := by
  ext i j
  rcases dna_cases i with rfl | rfl | rfl | rfl <;>
    rcases dna_cases j with rfl | rfl | rfl | rfl
  all_goals simp only [Matrix.mul_apply, sum_four]
  all_goals norm_num [generator, kernel, generatorIncrement, generatorSpectrum,
    Matrix.diagonal, hadamard, hadamardInverse, character, g1, g2, g3]
  all_goals ring

theorem exponential_diagonalization (a b : ℝ) :
    NormedSpace.exp (generator a b) =
      hadamard * Matrix.diagonal (fun g => Real.exp (generatorSpectrum a b g)) * hadamardInverse := by
  rw [generator_diagonalization]
  change NormedSpace.exp ((hadamardUnit : Matrix DNA DNA ℝ) *
      Matrix.diagonal (generatorSpectrum a b) * ((hadamardUnit⁻¹ : (Matrix DNA DNA ℝ)ˣ) : Matrix DNA DNA ℝ)) = _
  rw [Matrix.exp_units_conj, Matrix.exp_diagonal, Pi.exp_def]
  simp only [← Real.exp_eq_exp_ℝ]
  rfl

theorem generator_exp_formula (a b : ℝ) :
    NormedSpace.exp (generator a b) = k2Kernel (Real.exp (-2 * (a + b))) (Real.exp (-4 * b)) := by
  rw [exponential_diagonalization]
  ext i j
  rcases dna_cases i with rfl | rfl | rfl | rfl <;>
    rcases dna_cases j with rfl | rfl | rfl | rfl
  all_goals simp only [Matrix.mul_apply, sum_four]
  all_goals norm_num [k2Kernel, kernel, k2Increment, generatorSpectrum,
    Matrix.diagonal, hadamard, hadamardInverse, character, g1, g2, g3]
  all_goals ring

def PositiveRateTransition (M : Mat DNA) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ M = NormedSpace.exp (generator a b)

theorem positive_rate_ct2 {M : Mat DNA} (hM : PositiveRateTransition M) : CT2Strict M := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hM
  rw [generator_exp_formula]
  apply k2Kernel_ct2 (Real.exp_pos _) _ (Real.exp_pos _)
  · rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  · rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  · rw [pow_two, ← Real.exp_add]
    exact Real.exp_lt_exp.mpr (by linarith)

/-- Both independent rates are strictly positive. This is an exact
logarithmic inverse, not an assertion of embeddability from entry positivity. -/
theorem ct2_positive_rate {M : Mat DNA} (hM : CT2Strict M) : PositiveRateTransition M := by
  let x := eigen M g1
  let y := eigen M g3
  have hx := nucleotide_eigen hM.1 g1 (by decide)
  have hy := nucleotide_eigen hM.1 g3 (by decide)
  have hcone : x^2 < y := hM.2
  let b := -Real.log y / 4
  let a := (Real.log y - 2 * Real.log x) / 4
  have hb : 0 < b := by
    have hlog := Real.log_neg hy.1 hy.2
    dsimp [b]
    linarith
  have ha : 0 < a := by
    have hlog := Real.log_lt_log (sq_pos_of_pos hx.1) hcone
    rw [Real.log_pow] at hlog
    dsimp [a]
    norm_num at hlog
    linarith
  refine ⟨a, b, ha, hb, ?_⟩
  rw [generator_exp_formula]
  have hex : Real.exp (-2 * (a + b)) = x := by
    have he : -2 * (a + b) = Real.log x := by dsimp [a, b]; ring
    rw [he, Real.exp_log hx.1]
  have hey : Real.exp (-4 * b) = y := by
    have he : -4 * b = Real.log y := by dsimp [b]; ring
    rw [he, Real.exp_log hy.1]
  rw [hex, hey]
  exact nucleotide_k2_reconstruct hM.1

theorem positive_rate_iff_ct2 (M : Mat DNA) : PositiveRateTransition M ↔ CT2Strict M :=
  ⟨positive_rate_ct2, ct2_positive_rate⟩

section MaximalSource
open RootBlobEdgeIndexed RootBlobBoundaryGraph RootBlobMaximalSource RootBlobBinaryReplacement
open RootBlobRetainedPortGraph RootBlobRetainedPortModel RootBlobRetainedMaximal
open RootBlobRestrictedRetainedEndpoint
variable {V E O : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype O]
variable {G : RootBlobEdgeIndexed.Network V E O}

/-- The actual positive-rate generator class, not just a spectral name,
joined to the full original and admitted retained-fork observed-law images.
Both original cut matrices and every other exterior parameter stay fixed. -/
theorem maximal_positive_rate_fixed_exterior_admitted
    (B : MaximalRootTwoBlob G) (hG : GraphAdmitted G) (hB : BinaryAdmission G)
    (hNP : NoParallel G) (hLSA : RootLSA G)
    (W : E → ℝ) (hW : WeightsAdmitted G W)
    (MX : (B.component hG hB).OuterEdge → Mat DNA)
    (hMX : ∀ e, PositiveRateTransition (MX e)) :
    let R := B.component hG hB
    GraphAdmitted (R.retainedFork hG) ∧ NoParallel (R.retainedFork hG) ∧
    RootLSA (R.retainedFork hG) ∧
    WeightsAdmitted (R.retainedFork hG) (R.retainedWeights W) ∧
    RootBlobRestrictedRetainedEndpoint.fixedImage R W MX PositiveRateTransition =
      RootBlobRestrictedRetainedEndpoint.retainedImage R hG W MX PositiveRateTransition := by
  have hT : PositiveRateTransition = CT2Strict :=
    funext (fun M => propext (positive_rate_iff_ct2 M))
  have h := maximal_ct2_fixed_exterior_admitted B hG hB hNP hLSA W hW MX
    (fun e => positive_rate_ct2 (hMX e))
  simpa only [hT] using h

end MaximalSource

end RootBlobCT2GeneratorBridge
