import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
The actual least STRICT prefixSum crossing for exact finite branch weights.
Unlike a non-strict crossing, a boundary target never selects a zero-weight
branch, including target zero. This is deterministic arithmetic, not an RNG,
finite-precision or IID Boltzmann-law certificate.
-/

noncomputable section

namespace E8StrictPrefixSelector

open scoped BigOperators

def prefixSum (weight : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, weight j

theorem prefix_zero (weight : ℕ → ℝ) : prefixSum weight 0 = 0 := by
  simp [prefixSum]

theorem prefix_step (weight : ℕ → ℝ) (j : ℕ) :
    prefixSum weight (j + 1) = prefixSum weight j + weight j := by
  exact Finset.sum_range_succ _ _

theorem crossing_exists (n : ℕ) (weight : ℕ → ℝ) (target : ℝ)
    (htarget : 0 ≤ target) (hbelow : target < prefixSum weight n) :
    ∃ j : ℕ, j < n ∧ target < prefixSum weight (j + 1) := by
  have hn : 0 < n := by
    by_contra hn
    have : n = 0 := by omega
    subst n
    rw [prefix_zero] at hbelow
    linarith
  refine ⟨n - 1, by omega, ?_⟩
  have hstep : n - 1 + 1 = n := by omega
  simpa only [hstep] using hbelow

def select (n : ℕ) (weight : ℕ → ℝ) (target : ℝ)
    (htarget : 0 ≤ target) (hbelow : target < prefixSum weight n) : ℕ := by
  classical
  exact Nat.find (crossing_exists n weight target htarget hbelow)

theorem selected_interval (n : ℕ) (weight : ℕ → ℝ) (target : ℝ)
    (htarget : 0 ≤ target) (hbelow : target < prefixSum weight n) :
    let j := select n weight target htarget hbelow
    j < n ∧ prefixSum weight j ≤ target ∧ target < prefixSum weight (j + 1) := by
  classical
  let h := crossing_exists n weight target htarget hbelow
  change Nat.find h < n ∧ prefixSum weight (Nat.find h) ≤ target ∧
    target < prefixSum weight (Nat.find h + 1)
  have hs := Nat.find_spec h
  refine ⟨hs.1, ?_, hs.2⟩
  by_cases hj : Nat.find h = 0
  · simpa only [hj, prefix_zero] using htarget
  · have hm : Nat.find h - 1 < Nat.find h := by omega
    have hmin := Nat.find_min h hm
    have hprev : Nat.find h - 1 + 1 = Nat.find h := by omega
    apply le_of_not_gt
    intro hgt
    apply hmin
    refine ⟨by omega, ?_⟩
    simpa only [hprev] using hgt

theorem selected_weight_positive (n : ℕ) (weight : ℕ → ℝ) (target : ℝ)
    (htarget : 0 ≤ target) (hbelow : target < prefixSum weight n) :
    0 < weight (select n weight target htarget hbelow) := by
  have hi := selected_interval n weight target htarget hbelow
  have hp := prefix_step weight (select n weight target htarget hbelow)
  linarith [hi.2.1, hi.2.2]

theorem zero_weight_unreachable (n : ℕ) (weight : ℕ → ℝ) (target : ℝ)
    (htarget : 0 ≤ target) (hbelow : target < prefixSum weight n) (j : ℕ)
    (hzero : weight j = 0) :
    select n weight target htarget hbelow ≠ j := by
  intro heq
  have hp := selected_weight_positive n weight target htarget hbelow
  rw [heq, hzero] at hp
  exact lt_irrefl 0 hp

theorem prefix_monotone (n : ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ j < n, 0 ≤ weight j) {j k : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) :
    prefixSum weight j ≤ prefixSum weight k := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hjk
  · intro a ha _
    exact hweight a (lt_of_lt_of_le (Finset.mem_range.mp ha) hkn)

/-- Exact deterministic preimage interval. For continuous uniform u this
becomes the usual interval-length law after a separate measure calculation. -/
theorem selection_iff_interval (n : ℕ) (weight : ℕ → ℝ) (target : ℝ)
    (hweight : ∀ j < n, 0 ≤ weight j)
    (htarget : 0 ≤ target) (hbelow : target < prefixSum weight n) (j : ℕ) :
    select n weight target htarget hbelow = j ↔
      j < n ∧ prefixSum weight j ≤ target ∧ target < prefixSum weight (j + 1) := by
  classical
  constructor
  · intro heq
    simpa only [heq] using selected_interval n weight target htarget hbelow
  · rintro ⟨hjn, hjlo, hjhi⟩
    apply (Nat.find_eq_iff (crossing_exists n weight target htarget hbelow)).mpr
    refine ⟨⟨hjn, hjhi⟩, ?_⟩
    intro m hm hcross
    have hpre : prefixSum weight (m + 1) ≤ prefixSum weight j :=
      prefix_monotone n weight hweight (by omega) (by omega)
    linarith [hcross.2]

theorem uniform_target_valid (n : ℕ) (weight : ℕ → ℝ) (u : ℝ)
    (hpositive : 0 < prefixSum weight n) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ u * prefixSum weight n ∧ u * prefixSum weight n < prefixSum weight n := by
  constructor
  · exact mul_nonneg hu0 (le_of_lt hpositive)
  · have h := mul_lt_mul_of_pos_right hu1 hpositive
    simpa using h

end E8StrictPrefixSelector

#print axioms E8StrictPrefixSelector.crossing_exists
#print axioms E8StrictPrefixSelector.selected_interval
#print axioms E8StrictPrefixSelector.selected_weight_positive
#print axioms E8StrictPrefixSelector.zero_weight_unreachable
#print axioms E8StrictPrefixSelector.prefix_monotone
#print axioms E8StrictPrefixSelector.selection_iff_interval
#print axioms E8StrictPrefixSelector.uniform_target_valid
