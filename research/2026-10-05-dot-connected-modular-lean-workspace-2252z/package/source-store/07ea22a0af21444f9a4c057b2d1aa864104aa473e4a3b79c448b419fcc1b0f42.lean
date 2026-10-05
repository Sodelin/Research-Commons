import E8UniformPrefixLaw
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

/-!
The exact finite midpoint grid used by uniform_open52, parameterized by its
size N. Grid law means uniform counting on the N grid points. Uniformity or
independence of mt19937_64 engine words and IEEE/long-double scan arithmetic
are not proved here. Bounds apply to the exact-real strict selector.
-/
noncomputable section
namespace E8MidpointGridLaw
open E8StrictPrefixSelector E8UniformPrefixLaw
open scoped BigOperators

def midpoint (N k : ℕ) : ℝ := ((k : ℝ) + 1 / 2) / N

def cutoff (N : ℕ) (a : ℝ) : ℕ := Nat.ceil ((N : ℝ) * a - 1 / 2)

theorem midpoint_in_domain (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : k < N) :
    midpoint N k ∈ Set.Ico (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkr : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  constructor
  · unfold midpoint
    apply div_nonneg _ hNr.le
    positivity
  · unfold midpoint
    apply (div_lt_one hNr).mpr
    linarith

theorem midpoint_lt_iff_cutoff (N : ℕ) (hN : 0 < N) (k : ℕ) (a : ℝ) :
    midpoint N k < a ↔ k < cutoff N a := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [cutoff, Nat.lt_ceil, midpoint, div_lt_iff₀ hNr]
  constructor <;> intro h <;> nlinarith

theorem cutoff_mono (N : ℕ) {a b : ℝ} (hab : a ≤ b) : cutoff N a ≤ cutoff N b := by
  apply Nat.ceil_mono
  gcongr

theorem cutoff_le_size (N : ℕ) {a : ℝ} (ha : a ≤ 1) : cutoff N a ≤ N := by
  rw [cutoff, Nat.ceil_le]
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

theorem cutoff_zero (N : ℕ) : cutoff N 0 = 0 := by
  rw [cutoff, Nat.ceil_eq_zero]
  norm_num

theorem cutoff_one (N : ℕ) : cutoff N 1 = N := by
  by_cases hN : N = 0
  · subst N
    simp [cutoff]
  · apply le_antisymm (cutoff_le_size N (le_refl 1))
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
    have hn : N - 1 < cutoff N 1 := by
      rw [cutoff, Nat.lt_ceil]
      have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN)]
        simp
      rw [hcast]
      linarith
    omega

theorem cutoff_deviation (N : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    |(cutoff N a : ℝ) - (N : ℝ) * a| ≤ 1 / 2 := by
  have hlo := Nat.le_ceil ((N : ℝ) * a - 1 / 2)
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hgt : (-1 : ℝ) < (N : ℝ) * a - 1 / 2 := by nlinarith
  have hhi := Nat.ceil_lt_add_one_of_gt_neg_one hgt
  apply abs_le.mpr
  constructor <;> dsimp [cutoff] <;> linarith

theorem grid_prefix_set (N : ℕ) (hN : 0 < N) (a : ℝ) (ha : a ≤ 1) :
    (Finset.range N).filter (fun k => midpoint N k < a) = Finset.range (cutoff N a) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, midpoint_lt_iff_cutoff N hN]
  exact ⟨And.right, fun h => ⟨lt_of_lt_of_le h (cutoff_le_size N ha), h⟩⟩

theorem grid_interval_set (N : ℕ) (hN : 0 < N) (a b : ℝ) (hb : b ≤ 1) :
    (Finset.range N).filter (fun k => midpoint N k ∈ Set.Ico a b) =
      Finset.Ico (cutoff N a) (cutoff N b) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico, Finset.mem_Ico]
  have ha : a ≤ midpoint N k ↔ cutoff N a ≤ k := by
    rw [← not_lt, midpoint_lt_iff_cutoff N hN, not_lt]
  rw [ha, midpoint_lt_iff_cutoff N hN]
  exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h.2 (cutoff_le_size N hb), h⟩⟩

theorem grid_interval_card (N : ℕ) (hN : 0 < N) (a b : ℝ) (hb : b ≤ 1) :
    ((Finset.range N).filter (fun k => midpoint N k ∈ Set.Ico a b)).card =
      cutoff N b - cutoff N a := by
  rw [grid_interval_set N hN a b hb, Nat.card_Ico]

def gridBranchMass (N n : ℕ) (weight : ℕ → ℝ)
    (hpositive : 0 < prefixSum weight n) (j : ℕ) : ℝ :=
  (((Finset.range N).filter
    (fun k => uniformSelect n weight hpositive (midpoint N k) = j)).card : ℝ) / N

theorem branch_grid_count (N : ℕ) (hN : 0 < N) (n : ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ j < n, 0 ≤ weight j) (hpositive : 0 < prefixSum weight n)
    (j : ℕ) (hj : j < n) :
    ((Finset.range N).filter
      (fun k => uniformSelect n weight hpositive (midpoint N k) = j)).card =
      cutoff N (prefixSum weight (j + 1) / prefixSum weight n) -
      cutoff N (prefixSum weight j / prefixSum weight n) := by
  have hi := branch_preimage_interval n weight hweight hpositive j hj
  have heq : (Finset.range N).filter
      (fun k => uniformSelect n weight hpositive (midpoint N k) = j) =
      (Finset.range N).filter (fun k => midpoint N k ∈
        Set.Ico (prefixSum weight j / prefixSum weight n)
          (prefixSum weight (j + 1) / prefixSum weight n)) := by
    congr 1
    funext k
    exact propext (Set.ext_iff.mp hi (midpoint N k))
  rw [heq, grid_interval_card N hN]
  exact (interval_bounds n weight hweight hpositive j hj).2

theorem branch_grid_error (N : ℕ) (hN : 0 < N) (n : ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ j < n, 0 ≤ weight j) (hpositive : 0 < prefixSum weight n)
    (j : ℕ) (hj : j < n) :
    |gridBranchMass N n weight hpositive j - weight j / prefixSum weight n| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let a := prefixSum weight j / prefixSum weight n
  let b := prefixSum weight (j + 1) / prefixSum weight n
  have ha : 0 ≤ a := (interval_bounds n weight hweight hpositive j hj).1
  have hab : a ≤ b := (div_le_div_iff_of_pos_right hpositive).mpr
    (prefix_monotone n weight hweight (by omega) (by omega))
  have hb : 0 ≤ b := le_trans ha hab
  have hcuts := cutoff_mono N hab
  have haerr := cutoff_deviation N a ha
  have hberr := cutoff_deviation N b hb
  have hreal : ((cutoff N b - cutoff N a : ℕ) : ℝ) =
      (cutoff N b : ℝ) - (cutoff N a : ℝ) := Nat.cast_sub hcuts
  have hdiff : b - a = weight j / prefixSum weight n := by
    dsimp [a, b]
    rw [prefix_step, add_div]
    ring
  unfold gridBranchMass
  rw [branch_grid_count N hN n weight hweight hpositive j hj]
  change |((cutoff N b - cutoff N a : ℕ) : ℝ) / N - _| ≤ _
  rw [hreal, ← hdiff]
  obtain ⟨haerrlo, haerrhi⟩ := abs_le.mp haerr
  obtain ⟨hberrlo, hberrhi⟩ := abs_le.mp hberr
  have hid : ((cutoff N b : ℝ) - (cutoff N a : ℝ)) / N - (b - a) =
      (((cutoff N b : ℝ) - (cutoff N a : ℝ)) - (N : ℝ) * (b - a)) / N := by
    field_simp
  rw [hid, abs_div, abs_of_pos hNr]
  apply div_le_div_of_nonneg_right _ hNr.le
  apply abs_le.mpr
  constructor <;> nlinarith

end E8MidpointGridLaw
#print axioms E8MidpointGridLaw.midpoint_lt_iff_cutoff
#print axioms E8MidpointGridLaw.cutoff_deviation
#print axioms E8MidpointGridLaw.branch_grid_count
#print axioms E8MidpointGridLaw.branch_grid_error
