import G4AllRootPairClocks
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Arbitrary-order Kingman no-merger Hankel obstruction

New proof contribution: dot's active source-assumption-first Lean lane,
2026-10-02. The finite independent original-live-pair clock model from
G4AllRootPairClocks supplies the sequence exp(-t)^(n.choose 2).
Every finite, arbitrarily shifted Hankel block of this sequence is nonsingular
when t > 0. Thus ordinary add-one-root no-merger observations do not admit a
finite constant-coefficient linear recurrence, even eventually.

This rules out a proposed finite-Hankel/flatness shortcut. It does not assert
finite stopping for G4, identify the entire Kingman source process, or supply
an equivalence oracle. The algebraic result is stronger: every real q > 0,
q != 1, has the same nonsingularity obstruction.
-/

namespace GProgram.G4.Hankel

open scoped BigOperators
open Matrix

lemma choose_two_add (i j : ℕ) :
    (i + j).choose 2 = i.choose 2 + j.choose 2 + i * j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, Nat.choose_succ_succ, Nat.choose_one_right, ih,
      Nat.choose_succ_succ, Nat.choose_one_right, Nat.mul_succ]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
    omega

def noMergerSequence (q : ℝ) (k : ℕ) : ℝ := q ^ (k.choose 2)

def shiftedHankel (q : ℝ) (shift n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => noMergerSequence q (shift + i.val + j.val)

lemma noMergerSequence_add (q : ℝ) (i j : ℕ) :
    noMergerSequence q (i + j) =
      noMergerSequence q i * (q ^ i) ^ j * noMergerSequence q j := by
  simp only [noMergerSequence, choose_two_add, pow_add, pow_mul]
  ring

/-- Explicit source-sequence factorization through a Vandermonde matrix,
with strictly nonzero row and column scalings. -/
theorem shiftedHankel_factorization (q : ℝ) (shift n : ℕ) :
    shiftedHankel q shift n =
      diagonal (fun i : Fin n => noMergerSequence q (shift + i.val)) *
      vandermonde (fun i : Fin n => q ^ (shift + i.val)) *
      diagonal (fun j : Fin n => noMergerSequence q j.val) := by
  ext i j
  simp only [shiftedHankel, mul_diagonal, diagonal_mul, vandermonde_apply]
  exact noMergerSequence_add q (shift + i.val) j.val

theorem shifted_nodes_injective {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    (shift n : ℕ) : Function.Injective (fun i : Fin n => q ^ (shift + i.val)) := by
  intro i j hij
  have hv := pow_right_injective₀ hq hq1 hij
  apply Fin.ext
  omega

/-- Arbitrary finite order AND arbitrary starting root-count shift. No
uniform finite Hankel rank or eventual flatness can hold for this sequence. -/
theorem shiftedHankel_det_ne_zero {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    (shift n : ℕ) : (shiftedHankel q shift n).det ≠ 0 := by
  rw [shiftedHankel_factorization, det_mul, det_mul, det_diagonal, det_diagonal]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ hq.ne')
    · exact det_vandermonde_ne_zero_iff.mpr (shifted_nodes_injective hq hq1 shift n)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ hq.ne')

/-- Any putative order-n constant-coefficient recurrence already fails on
its first n test indices, at any fixed starting root-count shift. -/
theorem finite_window_coefficients_zero {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    (shift n : ℕ) (c : Fin n → ℝ)
    (h : ∀ i : Fin n, ∑ j : Fin n,
      noMergerSequence q (shift + i.val + j.val) * c j = 0) : c = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero (shiftedHankel_det_ne_zero hq hq1 shift n)
  funext i
  simpa only [Matrix.mulVec, dotProduct, shiftedHankel, Pi.zero_apply] using h i

/-- In particular there is no nontrivial eventually valid finite linear
recurrence, even with arbitrary real coefficients and a freely chosen shift. -/
theorem eventual_recurrence_coefficients_zero {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    (shift n : ℕ) (c : Fin n → ℝ)
    (h : ∀ i : ℕ, ∑ j : Fin n,
      noMergerSequence q (shift + i + j.val) * c j = 0) : c = 0 := by
  exact finite_window_coefficients_zero hq hq1 shift n c (fun i => h i.val)

/-- Observed no-first-merger probability in the ACTUAL finite independent
unordered-live-pair exponential clock product model, not an assumed sequence. -/
noncomputable def pairClockSurvival (duration : ℝ) (k : ℕ) : ℝ :=
  (GProgram.G4.PairClocks.pairClockMeasure k
    (GProgram.G4.PairClocks.noFirstMergeEvent k duration)).toReal

theorem pairClockSurvival_eq {duration : ℝ} (ht : 0 ≤ duration) (k : ℕ) :
    pairClockSurvival duration k = noMergerSequence (Real.exp (-duration)) k := by
  exact GProgram.G4.PairClocks.all_root_no_first_merge k ht

/-- The full-rank obstruction specializes to every strictly positive duration
of the admitted independent live-pair clock primitive. -/
theorem source_clock_eventual_recurrence_coefficients_zero {duration : ℝ}
    (ht : 0 < duration) (shift n : ℕ) (c : Fin n → ℝ)
    (h : ∀ i : ℕ, ∑ j : Fin n,
      pairClockSurvival duration (shift + i + j.val) * c j = 0) : c = 0 := by
  apply eventual_recurrence_coefficients_zero (Real.exp_pos (-duration))
    (ne_of_lt (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht))) shift n c
  intro i
  simpa only [pairClockSurvival_eq ht.le] using h i

#print axioms choose_two_add
#print axioms shiftedHankel_factorization
#print axioms shiftedHankel_det_ne_zero
#print axioms finite_window_coefficients_zero
#print axioms eventual_recurrence_coefficients_zero
#print axioms pairClockSurvival_eq
#print axioms source_clock_eventual_recurrence_coefficients_zero

end GProgram.G4.Hankel
