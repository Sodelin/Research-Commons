import BinaryIndicatorLawFactorization
import Mathlib.Tactic.Ring

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Standard binary conditional-independence cross-product equations on one
positive conditioning slice, and their equivalence to equality of the
two normalized row laws. The input is the actual four cell masses when
applied downstream, not an independence or invariance oracle premise.
Actual cylinder partition and source-law composition are separate lemmas.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

def binaryDeterminant (mass : Bool → Bool → ℚ) : ℚ :=
  mass false false * mass true true - mass false true * mass true false

def BinaryMassIndependent (mass : Bool → Bool → ℚ) : Prop :=
  ∀ i b, mass i b * (mass false false + mass false true + mass true false + mass true true) =
    (mass i false + mass i true) * (mass false b + mass true b)

def BinaryRowsEqual (mass : Bool → Bool → ℚ) : Prop :=
  ∀ b, mass false b / (mass false false + mass false true) =
    mass true b / (mass true false + mass true true)

theorem binary_cross_product_difference (mass : Bool → Bool → ℚ) (i b : Bool) :
    mass i b * (mass false false + mass false true + mass true false + mass true true) -
      (mass i false + mass i true) * (mass false b + mass true b) =
    if i = b then binaryDeterminant mass else -binaryDeterminant mass := by
  cases i <;> cases b <;> simp [binaryDeterminant] <;> ring

theorem binary_independent_iff_determinant (mass : Bool → Bool → ℚ) :
    BinaryMassIndependent mass ↔ binaryDeterminant mass = 0 := by
  constructor
  · intro independent
    have zero := sub_eq_zero.mpr (independent false false)
    rw [binary_cross_product_difference] at zero
    simpa (config := {instances := true}) using zero
  · intro determinant i b
    apply sub_eq_zero.mp
    rw [binary_cross_product_difference, determinant]
    by_cases same : i = b <;> simp (config := {instances := true}) [same]

theorem binary_rows_equal_iff_determinant (mass : Bool → Bool → ℚ)
    (rowZero : mass false false + mass false true ≠ 0)
    (rowOne : mass true false + mass true true ≠ 0) :
    BinaryRowsEqual mass ↔ binaryDeterminant mass = 0 := by
  have falseEntry :
      mass false false / (mass false false + mass false true) =
        mass true false / (mass true false + mass true true) ↔ binaryDeterminant mass = 0 := by
    rw [div_eq_div_iff rowZero rowOne, ← sub_eq_zero]
    have identity : mass false false * (mass true false + mass true true) -
        mass true false * (mass false false + mass false true) = binaryDeterminant mass := by
      unfold binaryDeterminant
      ring
    rw [identity]
  constructor
  · intro sameRows
    exact falseEntry.mp (sameRows false)
  · intro determinant b
    cases b with
    | false => exact falseEntry.mpr determinant
    | true =>
        apply (div_eq_div_iff rowZero rowOne).mpr
        apply sub_eq_zero.mp
        calc
          mass false true * (mass true false + mass true true) -
              mass true true * (mass false false + mass false true) = -binaryDeterminant mass := by
            unfold binaryDeterminant
            ring
          _ = 0 := by rw [determinant, neg_zero]

theorem binary_independent_iff_rows_equal (mass : Bool → Bool → ℚ)
    (rowZero : mass false false + mass false true ≠ 0)
    (rowOne : mass true false + mass true true ≠ 0) :
    BinaryMassIndependent mass ↔ BinaryRowsEqual mass :=
  (binary_independent_iff_determinant mass).trans
    (binary_rows_equal_iff_determinant mass rowZero rowOne).symm

end RestrictedCausal.ProbabilitySource.BinaryCPT
