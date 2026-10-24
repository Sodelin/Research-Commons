import RawNanuq
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Partial formal integration of OLD CB-NANUQ-005 (29 September).
The actual raw DISTINCT-quartet convention and 2n-4 baseline are reused.
At-most-two actual resolutions is an explicit source-side hypothesis;
outer-face/semidirected admission and the full support theorem are separate.
No estimator or circular-order finder is assumed implemented. -/
noncomputable section
namespace ResearchCommons.NANUQ.RawNoise
open scoped BigOperators
open Nanuq.Quartet Nanuq.Weighted Nanuq.Source.RootedBinary

/-- The original finite SET mean, including empty-set zero, lies on the
half-integer grid when no three different resolutions are present. -/
theorem distinct_mean_twice_integer (s : Finset Resolution) (small : s.card ≤ 2) :
    ∃ k : ℤ, 2 * distinctMean s = (k : ℚ) := by
  classical
  let a := Resolution.xy_zw
  let b := Resolution.xz_yw
  let c := Resolution.xw_yz
  have classify : s = (if a ∈ s then {a} else ∅) ∪
      (if b ∈ s then {b} else ∅) ∪ (if c ∈ s then {c} else ∅) := by
    ext r
    cases r <;> simp [a, b, c]
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> by_cases hc : c ∈ s
  all_goals rw [classify] at small ⊢
  all_goals simp only [ha, hb, hc, if_true, if_false, Finset.empty_union,
    Finset.union_empty] at small ⊢
  all_goals norm_num [a, b, c] at small
  all_goals first
    | exact ⟨0, by norm_num [distinctMean, separatesFirstPair, a, b, c]⟩
    | exact ⟨1, by norm_num [distinctMean, separatesFirstPair, a, b, c]⟩
    | exact ⟨2, by norm_num [distinctMean, separatesFirstPair, a, b, c]⟩

/-- Integrality is derived from literal scaled quartet entries, rather than
supplied as an equality with an integer distance matrix. -/
theorem source_nanuq_integer {n : ℕ} (rho : QuartetData n)
    (grid : ∀ x y p q, ∃ k : ℤ, 2 * rho x y p q = (k : ℚ)) (x y : Fin n) :
    ∃ k : ℤ, sourceNanuq rho x y = (k : ℚ) := by
  classical
  choose count hcount using grid
  by_cases hxy : x = y
  · exact ⟨0, by simp [sourceNanuq, hxy]⟩
  · refine ⟨(∑ p, ∑ q, if p < q ∧ outside x y p ∧ outside x y q
        then count x y p q else 0) + 2 * (n : ℤ) - 4, ?_⟩
    simp only [sourceNanuq, if_neg hxy, Finset.mul_sum, mul_ite, mul_zero]
    simp_rw [hcount]
    push_cast

/-- A hypothesis on actual raw graph switching sets, not an assumed desired
matrix/readout law. Deriving it for EVERY admitted plane source remains a join. -/
theorem raw_source_integer {V E : Type*} {n : ℕ}
    [Fintype V] [Fintype E] [DecidableEq V]
    (N : Nanuq.Source.RootedBinary V E (Fin n))
    (two : ∀ q : Fin 4 ↪ Fin n, (N.rawDisplayedQuartets q).card ≤ 2) (x y : Fin n) :
    ∃ k : ℤ, N.rawNanuq x y = (k : ℚ) := by
  apply source_nanuq_integer N.rawRho
  intro a b p q
  by_cases valid : ValidFour a b p q
  · rw [N.rawRho_valid a b p q valid]
    exact distinct_mean_twice_integer _ (two (fourTaxa a b p q valid))
  · exact ⟨0, by simp [rawRho, valid]⟩

/-- Existing pinned round_eq_iff; strict error rules out EVERY tie. -/
theorem round_of_abs_sub_lt_half {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] (x : K) (k : ℤ)
    (noise : |x - (k : K)| < 1 / 2) : round x = k := by
  apply round_eq_iff.mpr
  rcases abs_lt.mp noise with ⟨lower, upper⟩
  constructor <;> linarith

theorem integer_matrix_rounding {I J : Type*} (observed : I → J → ℚ)
    (truth : I → J → ℤ)
    (noise : ∀ i j, |observed i j - (truth i j : ℚ)| < 1 / 2) :
    (fun i j => round (observed i j)) = truth := by
  funext i j
  exact round_of_abs_sub_lt_half _ _ (noise i j)

/-- Real-valued observations of the SAME original unnormalized raw matrix.
This gives matrix recovery; the supplied correct circle/support theorem
is still needed to turn it into source split recovery. -/
theorem raw_source_rounding {V E : Type*} {n : ℕ}
    [Fintype V] [Fintype E] [DecidableEq V]
    (N : Nanuq.Source.RootedBinary V E (Fin n))
    (two : ∀ q : Fin 4 ↪ Fin n, (N.rawDisplayedQuartets q).card ≤ 2)
    (observed : Fin n → Fin n → ℝ)
    (noise : ∀ i j, |observed i j - (N.rawNanuq i j : ℝ)| < 1 / 2) (i j : Fin n) :
    (round (observed i j) : ℝ) = (N.rawNanuq i j : ℝ) := by
  obtain ⟨k, hk⟩ := raw_source_integer N two i j
  have real_eq : (N.rawNanuq i j : ℝ) = (k : ℝ) := by exact_mod_cast hk
  have bound := noise i j
  rw [real_eq] at bound ⊢
  rw [round_of_abs_sub_lt_half _ _ bound]

end ResearchCommons.NANUQ.RawNoise
