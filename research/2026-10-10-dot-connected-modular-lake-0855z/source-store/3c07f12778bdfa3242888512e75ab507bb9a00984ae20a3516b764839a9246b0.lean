import E8MidpointGridLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Finite branch-table total variation for the exact-real midpoint selector.
The sharp boundary accounting costs (n-1)/(2N), not n/N, including zero weights
and strict boundary ties. This remains conditional on uniform finite-grid input,
and does not claim PRNG independence or floating-point correctness.
-/
noncomputable section
namespace E8MidpointGridTV
open E8StrictPrefixSelector E8UniformPrefixLaw E8MidpointGridLaw
open scoped BigOperators

def branchTV (n : ℕ) (p q : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range n, |p j - q j|) / 2

private theorem sum_range_shift (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, f (j + 1)) =
      (∑ j ∈ Finset.range n, f j) + f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, ih]
    ring

/-- Internal cumulative boundaries account for all branch discrepancies. -/
theorem adjacent_variation_bound (n : ℕ) (hn : 0 < n) (delta : ℕ → ℝ)
    (c : ℝ) (hzero : delta 0 = 0) (hend : delta n = 0)
    (hbound : ∀ j, 0 < j → j < n → |delta j| ≤ c) :
    (∑ j ∈ Finset.range n, |delta (j + 1) - delta j|) ≤ 2 * ((n - 1 : ℕ) : ℝ) * c := by
  have htri : (∑ j ∈ Finset.range n, |delta (j + 1) - delta j|) ≤
      (∑ j ∈ Finset.range n, (|delta (j + 1)| + |delta j|)) := by
    apply Finset.sum_le_sum
    intro j _
    simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (delta (j + 1)) 0 (delta j))
  have hshift := sum_range_shift (fun j => |delta j|) n
  simp only [hzero, hend, abs_zero, add_zero, sub_zero] at hshift
  have hlen : n - 1 + 1 = n := by omega
  have hshiftInterior := sum_range_shift (fun j => |delta j|) (n - 1)
  simp only [hzero, abs_zero, sub_zero] at hshiftInterior
  have hinterior : (∑ j ∈ Finset.range n, |delta j|) =
      ∑ j ∈ Finset.range (n - 1), |delta (j + 1)| := by
    rw [← hlen, Finset.sum_range_succ]
    exact hshiftInterior.symm
  have hsum : (∑ j ∈ Finset.range (n - 1), |delta (j + 1)|) ≤ (n - 1 : ℕ) * c := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n - 1), c := by
        apply Finset.sum_le_sum
        intro j hj
        apply hbound (j + 1) (by omega)
        have hjlt := Finset.mem_range.mp hj
        omega
      _ = _ := by simp
  rw [Finset.sum_add_distrib, hshift, hinterior] at htri
  linarith

theorem grid_cdf_error (N : ℕ) (hN : 0 < N) (a : ℝ) (ha : 0 ≤ a) :
    |(cutoff N a : ℝ) / N - a| ≤ 1 / (2 * N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcut := cutoff_deviation N a ha
  have heq : (cutoff N a : ℝ) / N - a = ((cutoff N a : ℝ) - N * a) / N := by
    field_simp
  rw [heq, abs_div, abs_of_pos hNr]
  calc
    _ ≤ (1 / 2 : ℝ) / (N : ℝ) := div_le_div_of_nonneg_right hcut hNr.le
    _ = (1 : ℝ) / (2 * (N : ℝ)) := by ring

theorem grid_branch_TV_bound (N : ℕ) (hN : 0 < N) (n : ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ j < n, 0 ≤ weight j) (hpositive : 0 < prefixSum weight n) :
    branchTV n (gridBranchMass N n weight hpositive)
      (fun j => weight j / prefixSum weight n) ≤ (n - 1 : ℕ) / (2 * N) := by
  have hn : 0 < n := by
    by_contra hn
    have : n = 0 := by omega
    subst n
    simpa [prefix_zero] using hpositive
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let a : ℕ → ℝ := fun j => prefixSum weight j / prefixSum weight n
  let delta : ℕ → ℝ := fun j => (cutoff N (a j) : ℝ) / N - a j
  have hzero : delta 0 = 0 := by simp [delta, a, prefix_zero, cutoff_zero]
  have hend : delta n = 0 := by
    simp [delta, a, div_self (ne_of_gt hpositive), cutoff_one, div_self (ne_of_gt hNr)]
  have hbound : ∀ j, 0 < j → j < n → |delta j| ≤ 1 / (2 * N) := by
    intro j _ hj
    exact grid_cdf_error N hN (a j) (interval_bounds n weight hweight hpositive j hj).1
  have heq : ∀ j < n, gridBranchMass N n weight hpositive j - weight j / prefixSum weight n =
      delta (j + 1) - delta j := by
    intro j hj
    have hab : a j ≤ a (j + 1) := (div_le_div_iff_of_pos_right hpositive).mpr
      (prefix_monotone n weight hweight (by omega) (by omega))
    have hcuts := cutoff_mono N hab
    unfold gridBranchMass
    rw [branch_grid_count N hN n weight hweight hpositive j hj, Nat.cast_sub hcuts]
    dsimp [delta, a]
    rw [prefix_step]
    ring
  have hsumEq : (∑ j ∈ Finset.range n,
      |gridBranchMass N n weight hpositive j - weight j / prefixSum weight n|) =
      ∑ j ∈ Finset.range n, |delta (j + 1) - delta j| := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [heq j (Finset.mem_range.mp hj)]
  have hvar := adjacent_variation_bound n hn delta (1 / (2 * N)) hzero hend hbound
  unfold branchTV
  rw [hsumEq]
  calc
    _ ≤ (2 * ((n - 1 : ℕ) : ℝ) * (1 / (2 * (N : ℝ)))) / 2 :=
      div_le_div_of_nonneg_right hvar (by norm_num)
    _ = ((n - 1 : ℕ) : ℝ) / (2 * (N : ℝ)) := by ring

end E8MidpointGridTV
#print axioms E8MidpointGridTV.adjacent_variation_bound
#print axioms E8MidpointGridTV.grid_cdf_error
#print axioms E8MidpointGridTV.grid_branch_TV_bound
