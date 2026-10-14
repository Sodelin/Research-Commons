import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Source binomial cancellation and diagonal tangent controls

Source-authored, UNCOMPILED. Contributor: delegated Codex, 14 October 2026.
Source: DIAGONAL-TANGENT-COUNTERCONTROL.md and source_diagonal_controls.py in
2026-10-14-g4-independent-astra-exact-fibre-0535z.

The all-arity result below is an algebraic identity for the actual binomial
summands. Weight and exponent symmetry are proved, rather than supplied as
hypotheses. Correspondence with analytic partial derivatives of the bigon
polynomial and the padded source kernel remains an explicit adapter gate.
The cap-four directional quantities are polynomial differentials; their
analytic derivative correspondence is likewise not claimed here.
-/

namespace G4DiagonalTangent

open scoped BigOperators

/-- The natural no-merger exponent. -/
def lam (n : ℕ) : ℕ := n.choose 2

/-- The same quadratic expression, in the coefficient field. -/
def lamR (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) - 1) / 2

theorem lam_succ (n : ℕ) : lam (n + 1) = lam n + n := by
  simp [lam, Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

theorem cast_lam (n : ℕ) : (lam n : ℝ) = lamR n := by
  induction n with
  | zero => norm_num [lam, lamR]
  | succ n ih =>
    rw [lam_succ, Nat.cast_add, ih]
    simp only [lamR, Nat.cast_add, Nat.cast_one]
    ring

/-- The actual independent-bigon summand; there are no abstract weights. -/
def bigonWeight (n k : ℕ) (x y g : ℝ) : ℝ :=
  (n.choose k : ℝ) * g ^ k * (1 - g) ^ (n - k) *
    x ^ lam k * y ^ lam (n - k)

def bigon (n : ℕ) (x y g : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), bigonWeight n k x y g

def diagonalWeight (n k : ℕ) (ρ : ℝ) : ℝ :=
  bigonWeight n k ρ ρ (1 / (1 + ρ))

/-- The exponent after combining the routing and arm factors. -/
def diagonalExponent (n k : ℕ) : ℕ :=
  n - k + lam k + lam (n - k)

theorem diagonalWeight_normal_form (n k : ℕ) (ρ : ℝ)
    (hk : k ≤ n) (hρ : 1 + ρ ≠ 0) :
    diagonalWeight n k ρ =
      (n.choose k : ℝ) * ρ ^ diagonalExponent n k / (1 + ρ) ^ n := by
  have hg : 1 - 1 / (1 + ρ) = ρ / (1 + ρ) := by
    field_simp [hρ]
    <;> ring
  have hkn : k + (n - k) = n := by omega
  unfold diagonalWeight bigonWeight
  rw [hg]
  simp only [one_div_pow, div_pow]
  calc
    (n.choose k : ℝ) * (1 / (1 + ρ) ^ k) *
        (ρ ^ (n - k) / (1 + ρ) ^ (n - k)) * ρ ^ lam k * ρ ^ lam (n - k)
      = (n.choose k : ℝ) *
          (ρ ^ (n - k) * ρ ^ lam k * ρ ^ lam (n - k)) /
          ((1 + ρ) ^ k * (1 + ρ) ^ (n - k)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
    _ = (n.choose k : ℝ) * ρ ^ diagonalExponent n k / (1 + ρ) ^ n := by
      rw [← pow_add, ← pow_add, ← pow_add, hkn]

/-- Source exponent symmetry on exactly the paired positive-root domain. -/
theorem diagonalExponent_reflect (n k : ℕ) (hk₀ : 1 ≤ k) (hk : k ≤ n) :
    diagonalExponent n (n + 1 - k) = diagonalExponent n k := by
  have hleft : n - (n + 1 - k) = k - 1 := by omega
  have hright : n + 1 - k = (n - k) + 1 := by omega
  have hsucc : k = (k - 1) + 1 := by omega
  have ha : lam k = lam (k - 1) + (k - 1) := by
    conv_lhs => rw [hsucc]
    exact lam_succ (k - 1)
  have hb : lam (n + 1 - k) = lam (n - k) + (n - k) := by
    rw [hright, lam_succ]
  unfold diagonalExponent
  rw [hleft, ha, hb]
  omega

/-- The actual binomial coefficient identity needed by the involution. -/
theorem binomial_weight_reflect (n k : ℕ) (hk₀ : 1 ≤ k) (hk : k ≤ n) :
    k * n.choose k = (n + 1 - k) * n.choose (n + 1 - k) := by
  have hsucc : k - 1 + 1 = k := by omega
  have hsub : n - (k - 1) = n + 1 - k := by omega
  have hchoose : n.choose (n + 1 - k) = n.choose (k - 1) := by
    rw [← hsub]
    exact Nat.choose_symm (by omega)
  have h := Nat.choose_succ_right_eq n (k - 1)
  rw [hsucc, hsub] at h
  rw [hchoose]
  simpa only [Nat.mul_comm] using h

/-- Weight symmetry derived from the original binomial summand. -/
theorem diagonalWeight_reflect (n k : ℕ) (ρ : ℝ)
    (hk₀ : 1 ≤ k) (hk : k ≤ n) (hρ : 1 + ρ ≠ 0) :
    (k : ℝ) * diagonalWeight n k ρ =
      ((n + 1 - k : ℕ) : ℝ) * diagonalWeight n (n + 1 - k) ρ := by
  have hj : n + 1 - k ≤ n := by omega
  have hc : (k : ℝ) * (n.choose k : ℝ) =
      ((n + 1 - k : ℕ) : ℝ) * (n.choose (n + 1 - k) : ℝ) := by
    have h := congrArg (fun q : ℕ => (q : ℝ))
      (binomial_weight_reflect n k hk₀ hk)
    simpa only [Nat.cast_mul] using h
  rw [diagonalWeight_normal_form n k ρ hk hρ,
    diagonalWeight_normal_form n (n + 1 - k) ρ hj hρ,
    diagonalExponent_reflect n k hk₀ hk]
  calc
    (k : ℝ) * ((n.choose k : ℝ) * ρ ^ diagonalExponent n k / (1 + ρ) ^ n)
      = ((k : ℝ) * (n.choose k : ℝ)) *
          (ρ ^ diagonalExponent n k / (1 + ρ) ^ n) := by ring
    _ = (((n + 1 - k : ℕ) : ℝ) * (n.choose (n + 1 - k) : ℝ)) *
          (ρ ^ diagonalExponent n k / (1 + ρ) ^ n) := by rw [hc]
    _ = _ := by ring

/-- General reindexing lemma. It alone does not prove source weight symmetry. -/
theorem sum_range_eq_zero_of_reflect_neg (n : ℕ) (f : ℕ → ℝ)
    (hf : ∀ i < n, f (n - 1 - i) = -f i) :
    (∑ i ∈ Finset.range n, f i) = 0 := by
  have h : (∑ i ∈ Finset.range n, f i) =
      -(∑ i ∈ Finset.range n, f i) := by
    calc
      (∑ i ∈ Finset.range n, f i) =
          ∑ i ∈ Finset.range n, f (n - 1 - i) :=
            (Finset.sum_range_reflect f n).symm
      _ = ∑ i ∈ Finset.range n, -f i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hf i (Finset.mem_range.mp hi)
      _ = _ := by rw [Finset.sum_neg_distrib]
  linarith

def cancellationTerm (n k : ℕ) (ρ : ℝ) : ℝ :=
  (k : ℝ) * diagonalWeight n k ρ * (2 * (k : ℝ) - (n : ℝ) - 1)

theorem positive_root_cancellation (n : ℕ) (ρ : ℝ) (hρ : 1 + ρ ≠ 0) :
    (∑ i ∈ Finset.range n, cancellationTerm n (i + 1) ρ) = 0 := by
  apply sum_range_eq_zero_of_reflect_neg
  intro i hi
  have hk : i + 1 ≤ n := by omega
  have he : n - 1 - i + 1 = n + 1 - (i + 1) := by omega
  have hc : (n + 1 - (i + 1) : ℕ) + (i + 1) = n + 1 := by omega
  have hcR : ((n + 1 - (i + 1) : ℕ) : ℝ) + ((i + 1 : ℕ) : ℝ) =
      (n : ℝ) + 1 := by
    have h := congrArg (fun q : ℕ => (q : ℝ)) hc
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hsign : 2 * ((n + 1 - (i + 1) : ℕ) : ℝ) - (n : ℝ) - 1 =
      -(2 * ((i + 1 : ℕ) : ℝ) - (n : ℝ) - 1) := by linarith
  unfold cancellationTerm
  rw [he, ← diagonalWeight_reflect n (i + 1) ρ (by omega) hk hρ]
  rw [hsign]
  ring

theorem quadratic_coefficient_identity (n k : ℕ) (hk : k ≤ n) :
    3 * lamR k + lamR (n - k) - lamR n =
      (k : ℝ) * (2 * (k : ℝ) - (n : ℝ) - 1) := by
  unfold lamR
  rw [Nat.cast_sub hk]
  ring

/-- Formal polynomial differential residual, prior to the analytic adapter. -/
def wardResidual (n : ℕ) (ρ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), diagonalWeight n k ρ *
    (3 * lamR k + lamR (n - k) - lamR n)

/-- All arities, including 0 and 1, for the actual source binomial formula. -/
theorem wardResidual_zero (n : ℕ) (ρ : ℝ) (hρ : 1 + ρ ≠ 0) :
    wardResidual n ρ = 0 := by
  have hsum : wardResidual n ρ =
      ∑ k ∈ Finset.range (n + 1), cancellationTerm n k ρ := by
    unfold wardResidual
    apply Finset.sum_congr rfl
    intro k hk
    rw [quadratic_coefficient_identity n k (by
      have := Finset.mem_range.mp hk
      omega)]
    unfold cancellationTerm
    ring
  rw [hsum, Finset.sum_range_succ']
  simpa only [cancellationTerm, Nat.cast_zero, zero_mul, add_zero, zero_add] using
    positive_root_cancellation n ρ hρ

theorem fixed_target_all_arity_residual (n : ℕ) :
    wardResidual n (1 / 2) = 0 := by
  apply wardResidual_zero
  norm_num

/-- Equivalent finite-sum form of the all-arity Ward identity. -/
theorem source_weighted_ward_identity (n : ℕ) (ρ : ℝ) (hρ : 1 + ρ ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), diagonalWeight n k ρ *
      (3 * lamR k + lamR (n - k))) =
        lamR n * bigon n ρ ρ (1 / (1 + ρ)) := by
  have hz := wardResidual_zero n ρ hρ
  unfold wardResidual at hz
  simp only [mul_sub, Finset.sum_sub_distrib] at hz
  rw [← Finset.sum_mul] at hz
  calc
    _ = (∑ k ∈ Finset.range (n + 1), diagonalWeight n k ρ) * lamR n :=
      sub_eq_zero.mp hz
    _ = _ := by
      simpa only [bigon, diagonalWeight] using
        mul_comm (∑ k ∈ Finset.range (n + 1), diagonalWeight n k ρ) (lamR n)

/-- Explicit polynomial partial summands, including zero exponents. These are
formal differentials; their analytic interpretation remains an adapter gate. -/
def bigonDxWeight (n k : ℕ) (x y g : ℝ) : ℝ :=
  (n.choose k : ℝ) * g ^ k * (1 - g) ^ (n - k) *
    (lam k : ℝ) * x ^ (lam k - 1) * y ^ lam (n - k)

def bigonDyWeight (n k : ℕ) (x y g : ℝ) : ℝ :=
  (n.choose k : ℝ) * g ^ k * (1 - g) ^ (n - k) *
    x ^ lam k * (lam (n - k) : ℝ) * y ^ (lam (n - k) - 1)

def bigonDx (n : ℕ) (x y g : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), bigonDxWeight n k x y g

def bigonDy (n : ℕ) (x y g : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), bigonDyWeight n k x y g

theorem power_differential_mul (m : ℕ) (ρ : ℝ) :
    (m : ℝ) * ρ ^ (m - 1) * ρ = (m : ℝ) * ρ ^ m := by
  cases m with
  | zero => simp
  | succ m => simp only [Nat.succ_sub_one, pow_succ]; ring

theorem bigonDxWeight_mul (n k : ℕ) (ρ g : ℝ) :
    ρ * bigonDxWeight n k ρ ρ g = bigonWeight n k ρ ρ g * lamR k := by
  unfold bigonDxWeight bigonWeight
  calc
    _ = ((n.choose k : ℝ) * g ^ k * (1 - g) ^ (n - k)) *
        ((lam k : ℝ) * ρ ^ (lam k - 1) * ρ) * ρ ^ lam (n - k) := by ring
    _ = _ := by rw [power_differential_mul, cast_lam]; ring

theorem bigonDyWeight_mul (n k : ℕ) (ρ g : ℝ) :
    ρ * bigonDyWeight n k ρ ρ g = bigonWeight n k ρ ρ g * lamR (n - k) := by
  unfold bigonDyWeight bigonWeight
  calc
    _ = ((n.choose k : ℝ) * g ^ k * (1 - g) ^ (n - k)) * ρ ^ lam k *
        ((lam (n - k) : ℝ) * ρ ^ (lam (n - k) - 1) * ρ) := by ring
    _ = _ := by rw [power_differential_mul, cast_lam]; ring

/-- All-arity source polynomial-partial identity, with the original powers and
binomial routing factors present explicitly in both partial sums. -/
theorem source_polynomial_partial_identity (n : ℕ) (ρ : ℝ) (hρ : 1 + ρ ≠ 0) :
    ρ * (3 * bigonDx n ρ ρ (1 / (1 + ρ)) + bigonDy n ρ ρ (1 / (1 + ρ))) =
      lamR n * bigon n ρ ρ (1 / (1 + ρ)) := by
  have hx : ρ * bigonDx n ρ ρ (1 / (1 + ρ)) =
      ∑ k ∈ Finset.range (n + 1), diagonalWeight n k ρ * lamR k := by
    unfold bigonDx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact bigonDxWeight_mul n k ρ (1 / (1 + ρ))
  have hy : ρ * bigonDy n ρ ρ (1 / (1 + ρ)) =
      ∑ k ∈ Finset.range (n + 1), diagonalWeight n k ρ * lamR (n - k) := by
    unfold bigonDy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact bigonDyWeight_mul n k ρ (1 / (1 + ρ))
  calc
    _ = 3 * (ρ * bigonDx n ρ ρ (1 / (1 + ρ))) +
        ρ * bigonDy n ρ ρ (1 / (1 + ρ)) := by ring
    _ = 3 * (∑ k ∈ Finset.range (n + 1), diagonalWeight n k ρ * lamR k) +
        (∑ k ∈ Finset.range (n + 1), diagonalWeight n k ρ * lamR (n - k)) := by
          rw [hx, hy]
    _ = ∑ k ∈ Finset.range (n + 1), diagonalWeight n k ρ *
        (3 * lamR k + lamR (n - k)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := source_weighted_ward_identity n ρ hρ

/-- The actual pair coordinate of the padded one-bigon body. -/
def pairBody (a x y g r : ℝ) : ℝ :=
  (a * r) * (g ^ 2 * x + (1 - g) ^ 2 * y + 2 * g * (1 - g))

theorem pair_curve_identity (t : ℝ) :
    pairBody ((3 / 4) * (1 - t)) (1 / 2 + (3 / 2) * t)
      (1 / 2 + (1 / 2) * t) (2 / 3) (1 / 2) =
        (13 / 48) * (1 - t ^ 2) := by
  unfold pairBody
  ring

theorem pair_target_value : pairBody (3 / 4) (1 / 2) (1 / 2) (2 / 3) (1 / 2) =
    13 / 48 := by norm_num [pairBody]

theorem pair_curve_ne_target (t : ℝ) (ht : t ≠ 0) :
    pairBody ((3 / 4) * (1 - t)) (1 / 2 + (3 / 2) * t)
      (1 / 2 + (1 / 2) * t) (2 / 3) (1 / 2) ≠ 13 / 48 := by
  rw [pair_curve_identity]
  intro h
  have ht2 : t ^ 2 > 0 := sq_pos_of_ne_zero ht
  nlinarith

/-- Strict admissibility of the one physical tuple on the stated interval. -/
theorem strict_curve_parameters (t : ℝ) (hlo : -1 / 3 < t) (hhi : t < 1 / 3) :
    0 < (3 / 4) * (1 - t) ∧ (3 / 4) * (1 - t) < 1 ∧
    0 < 1 / 2 + (3 / 2) * t ∧ 1 / 2 + (3 / 2) * t < 1 ∧
    0 < 1 / 2 + (1 / 2) * t ∧ 1 / 2 + (1 / 2) * t < 1 ∧
    (0 : ℝ) < 2 / 3 ∧ (2 / 3 : ℝ) < 1 ∧
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by norm_num, by norm_num, by norm_num, by norm_num⟩

def V (z : ℝ) : ℝ := (2 - 3 * z + z ^ 3) / 6

def contrastB (x y g : ℝ) : ℝ :=
  2 * (g ^ 2 * (1 - g) ^ 2 * (1 - x) * (1 - y) -
    g ^ 3 * (1 - g) * V x - g * (1 - g) ^ 3 * V y)

/-- Explicit polynomial partials; no derivative theorem is imported. -/
def contrastBx (x y g : ℝ) : ℝ :=
  2 * (-g ^ 2 * (1 - g) ^ 2 * (1 - y) -
    g ^ 3 * (1 - g) * ((-3 + 3 * x ^ 2) / 6))

def contrastBy (x y g : ℝ) : ℝ :=
  2 * (-g ^ 2 * (1 - g) ^ 2 * (1 - x) -
    g * (1 - g) ^ 3 * ((-3 + 3 * y ^ 2) / 6))

/-- Exact coefficient extraction from the actual contrast polynomial. The
specified partial polynomials are therefore tied to the source formula. -/
theorem contrastB_increment (x y g dx dy t : ℝ) :
    contrastB (x + dx * t) (y + dy * t) g =
      contrastB x y g + t * (dx * contrastBx x y g + dy * contrastBy x y g) +
        t ^ 2 * (2 * (g ^ 2 * (1 - g) ^ 2 * dx * dy -
          g ^ 3 * (1 - g) * (x * dx ^ 2 / 2 + dx ^ 3 * t / 6) -
          g * (1 - g) ^ 3 * (y * dy ^ 2 / 2 + dy ^ 3 * t / 6))) := by
  unfold contrastB contrastBx contrastBy V
  ring

def contrastC (a x y g r : ℝ) : ℝ := a ^ 6 * r * contrastB x y g
def contrastH (a x y g r : ℝ) : ℝ := a ^ 6 * (1 - r) * contrastB x y g

/-- Polynomial differential along (-a,3/2,1/2,0,0). -/
def directionalC (a x y g r : ℝ) : ℝ :=
  a ^ 6 * r * (-6 * contrastB x y g +
    (3 / 2) * contrastBx x y g + (1 / 2) * contrastBy x y g)

def directionalH (a x y g r : ℝ) : ℝ :=
  a ^ 6 * (1 - r) * (-6 * contrastB x y g +
    (3 / 2) * contrastBx x y g + (1 / 2) * contrastBy x y g)

theorem cap_four_target_values :
    contrastB (1 / 2) (1 / 2) (2 / 3) = -1 / 972 ∧
    contrastBx (1 / 2) (1 / 2) (2 / 3) = 2 / 81 ∧
    contrastBy (1 / 2) (1 / 2) (2 / 3) = -5 / 162 ∧
    contrastC (3 / 4) (1 / 2) (1 / 2) (2 / 3) (1 / 2) = -3 / 32768 ∧
    contrastH (3 / 4) (1 / 2) (1 / 2) (2 / 3) (1 / 2) = -3 / 32768 := by
  norm_num [contrastB, contrastBx, contrastBy, contrastC, contrastH, V]

theorem cap_four_directional_values :
    directionalC (3 / 4) (1 / 2) (1 / 2) (2 / 3) (1 / 2) = 81 / 32768 ∧
    directionalH (3 / 4) (1 / 2) (1 / 2) (2 / 3) (1 / 2) = 81 / 32768 := by
  norm_num [directionalC, directionalH, contrastB, contrastBx, contrastBy, V]

def capFourCurveRemainder (t : ℝ) : ℝ :=
  (-540 + 1380 * t - 1098 * t ^ 2 - 1602 * t ^ 3 + 4404 * t ^ 4 -
    4140 * t ^ 5 + 1845 * t ^ 6 - 327 * t ^ 7) / 32768

/-- The coefficient 81/32768 is extracted from both actual padded contrast
polynomials, independently of the names given to their formal differentials. -/
theorem cap_four_curve_expansion (t : ℝ) :
    contrastC ((3 / 4) * (1 - t)) (1 / 2 + (3 / 2) * t)
      (1 / 2 + (1 / 2) * t) (2 / 3) (1 / 2) =
        -3 / 32768 + (81 / 32768) * t + t ^ 2 * capFourCurveRemainder t ∧
    contrastH ((3 / 4) * (1 - t)) (1 / 2 + (3 / 2) * t)
      (1 / 2 + (1 / 2) * t) (2 / 3) (1 / 2) =
        -3 / 32768 + (81 / 32768) * t + t ^ 2 * capFourCurveRemainder t := by
  constructor <;>
    simp only [contrastC, contrastH, contrastB, V, capFourCurveRemainder] <;> ring

#print axioms wardResidual_zero
#print axioms fixed_target_all_arity_residual
#print axioms source_weighted_ward_identity
#print axioms source_polynomial_partial_identity
#print axioms pair_curve_identity
#print axioms pair_curve_ne_target
#print axioms strict_curve_parameters
#print axioms contrastB_increment
#print axioms cap_four_target_values
#print axioms cap_four_directional_values
#print axioms cap_four_curve_expansion

end G4DiagonalTangent
