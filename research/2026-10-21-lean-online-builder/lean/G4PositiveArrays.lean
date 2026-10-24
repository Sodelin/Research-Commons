import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Finite-array interpolation requested by the existing G4 owner.
No source/kernel-observer adapter or analytic remainder bound is assumed here.
Nonnegative entries suffice, including empty arrays and zero total sum. -/
namespace G4CountUniform

open scoped BigOperators

theorem cubic_sum_interpolation {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i ^ 3) ^ 3 ≤
      (∑ i ∈ s, a i) * (∑ i ∈ s, a i ^ 4) ^ 2 := by
  let L := ∑ i ∈ s, a i
  let Q := ∑ i ∈ s, a i ^ 2
  let S := ∑ i ∈ s, a i ^ 3
  let R := ∑ i ∈ s, a i ^ 4
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i hi => sq_nonneg (a i)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i hi => pow_nonneg (ha i hi) 3
  have hR : 0 ≤ R := Finset.sum_nonneg fun i hi => pow_nonneg (ha i hi) 4
  have hQS : Q ^ 2 ≤ L * S := by
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s ha
      (fun i hi => pow_nonneg (ha i hi) 3)
      (r := fun i => a i ^ 2) (fun i hi => le_of_eq (by ring))
  have hSR : S ^ 2 ≤ Q * R := by
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i hi => sq_nonneg (a i))
      (fun i hi => pow_nonneg (ha i hi) 4)
      (r := fun i => a i ^ 3) (fun i hi => le_of_eq (by ring))
  have hSquare := mul_le_mul hSR hSR (sq_nonneg S) (mul_nonneg hQ hR)
  have hMultiply := mul_le_mul_of_nonneg_right hQS (sq_nonneg R)
  change S ^ 3 ≤ L * R ^ 2
  by_cases hz : S = 0
  · have hL : 0 ≤ L := Finset.sum_nonneg ha
    simpa [hz] using mul_nonneg hL (sq_nonneg R)
  · have hp : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    by_contra hn
    have hpos : 0 < S * (S ^ 3 - L * R ^ 2) :=
      mul_pos hp (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hSquare, hMultiply, hpos]

theorem sixth_cubic_interpolation {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i ^ 6) * (∑ i ∈ s, a i ^ 3) ≤
      (∑ i ∈ s, a i) * (∑ i ∈ s, a i ^ 4) ^ 2 := by
  have hS : 0 ≤ ∑ i ∈ s, a i ^ 3 :=
    Finset.sum_nonneg fun i hi => pow_nonneg (ha i hi) 3
  have hSix : (∑ i ∈ s, a i ^ 6) ≤ (∑ i ∈ s, a i ^ 3) ^ 2 := by
    simpa only [← pow_mul] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := s)
        (f := fun i => a i ^ 3) (fun i hi => pow_nonneg (ha i hi) 3))
  calc
    _ ≤ (∑ i ∈ s, a i ^ 3) ^ 2 * (∑ i ∈ s, a i ^ 3) :=
      mul_le_mul_of_nonneg_right hSix hS
    _ = (∑ i ∈ s, a i ^ 3) ^ 3 := by ring
    _ ≤ _ := cubic_sum_interpolation s a ha

end G4CountUniform
