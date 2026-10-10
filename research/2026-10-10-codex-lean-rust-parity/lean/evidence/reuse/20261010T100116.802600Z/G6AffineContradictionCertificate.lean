import G6RationalAffineWitness

/-!
# Exact original-row certificates for strict affine infeasibility

Contributor: Codex / lean_reuse, 10 October 2026.
This independently checks a nonnegative combination of the original rows.
Projection traces need not be trusted by a certificate consumer. A zero normal
with negative bound, or zero bound with a positively weighted strict premise,
excludes every real vector. The theorem concerns the supplied finite matrix;
source admission and complete source/chart coverage remain separate.
-/
namespace UnifiedLean.G6.AffineContradictionCertificate

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness
open scoped BigOperators

def weightedBound {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) : ℚ :=
  ∑ i, weights i * (rows i).bound

def weightedCoeff {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) (j : Fin n) : ℚ :=
  ∑ i, weights i * (rows i).coeff j

def StrictUsed {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) : Prop :=
  ∃ i, 0 < weights i ∧ (rows i).strict = true

def Valid {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) : Prop :=
  (∀ i, 0 ≤ weights i) ∧ (∀ j, weightedCoeff rows weights j = 0) ∧
    (weightedBound rows weights < 0 ∨
      (weightedBound rows weights = 0 ∧ StrictUsed rows weights))

def check {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) : Bool :=
  decide (Valid rows weights)

theorem check_correct {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) :
    check rows weights = true ↔ Valid rows weights := by
  simp only [check, decide_eq_true_eq]

theorem weighted_eval_eq {m n : ℕ} (rows : Fin m → Row n)
    (weights : Fin m → ℚ) (x : Fin n → ℝ) :
    (∑ i, (weights i : ℝ) * (rows i).eval x) =
      ∑ j, (weightedCoeff rows weights j : ℝ) * x j := by
  simp only [Row.eval, Finset.mul_sum, weightedCoeff, rat_cast_sum,
    Rat.cast_mul, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Soundness for arbitrary real vectors, with strict rows handled without
a closure relaxation. This excludes weak infeasibility as well as strict
boundary conflicts such as `x < 0` together with `0 ≤ x`. -/
theorem valid_excludes_real {m n : ℕ} (rows : Fin m → Row n)
    (weights : Fin m → ℚ) (hv : Valid rows weights) :
    ¬ ∃ x : Fin n → ℝ, ∀ i, (rows i).Holds x := by
  rintro ⟨x, hx⟩
  obtain ⟨hw, hc, hb⟩ := hv
  have he : (∑ i, (weights i : ℝ) * (rows i).eval x) = 0 := by
    rw [weighted_eval_eq]
    simp only [hc, Rat.cast_zero, zero_mul, Finset.sum_const_zero]
  have hle : ∀ i, (weights i : ℝ) * (rows i).eval x ≤
      (weights i : ℝ) * ((rows i).bound : ℝ) := by
    intro i
    apply mul_le_mul_of_nonneg_left (rel_le (hx i))
    exact_mod_cast hw i
  have hbcast : (∑ i, (weights i : ℝ) * ((rows i).bound : ℝ)) =
      (weightedBound rows weights : ℝ) := by
    simp only [weightedBound, rat_cast_sum, Rat.cast_mul]
  rcases hb with hneg | ⟨hzero, i, hi, hstrict⟩
  · have hsum := Finset.sum_le_sum (fun i _ => hle i)
    rw [he, hbcast] at hsum
    have hn : (weightedBound rows weights : ℝ) < 0 := by exact_mod_cast hneg
    linarith
  · have hrow : (rows i).eval x < ((rows i).bound : ℝ) := by
      simpa only [Row.Holds, Rel, hstrict, if_true] using hx i
    have hmul : (weights i : ℝ) * (rows i).eval x <
        (weights i : ℝ) * ((rows i).bound : ℝ) :=
      mul_lt_mul_of_pos_left hrow (by exact_mod_cast hi)
    have hsum := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hmul⟩
    rw [he, hbcast, hzero, Rat.cast_zero] at hsum
    exact (lt_irrefl (0 : ℝ)) hsum

theorem checked_excludes_real {m n : ℕ} (rows : Fin m → Row n)
    (weights : Fin m → ℚ) (h : check rows weights = true) :
    ¬ ∃ x : Fin n → ℝ, ∀ i, (rows i).Holds x :=
  valid_excludes_real rows weights ((check_correct rows weights).mp h)

#print axioms check_correct
#print axioms weighted_eval_eq
#print axioms valid_excludes_real
#print axioms checked_excludes_real

end UnifiedLean.G6.AffineContradictionCertificate
