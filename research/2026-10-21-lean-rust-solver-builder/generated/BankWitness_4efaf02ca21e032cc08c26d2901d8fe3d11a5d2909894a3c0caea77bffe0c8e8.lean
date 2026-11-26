import CMRationalBank
import Astra.Generated.Certificate_776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Astra.Generated.BankWitness_4efaf02ca21e032cc08c26d2901d8fe3d11a5d2909894a3c0caea77bffe0c8e8

open scoped BigOperators
open Astra.CommonMoment
open Astra.CommonMoment.RationalBank

def nodes : Finset ℚ := {((1 : ℚ) / (3 : ℚ)), ((2 : ℚ) / (3 : ℚ))}

def groupedWeight (q : ℚ) : ℚ :=
  if q = ((1 : ℚ) / (3 : ℚ)) then ((1 : ℚ) / (2 : ℚ)) else if q = ((2 : ℚ) / (3 : ℚ)) then ((1 : ℚ) / (2 : ℚ)) else (0 : ℚ)

def rawMoment (n : ℕ) : ℚ :=
  ((((1 : ℚ) / (4 : ℚ)) * ((1 : ℚ) / (3 : ℚ))^n + ((1 : ℚ) / (4 : ℚ)) * ((2 : ℚ) / (6 : ℚ))^n) + (((1 : ℚ) / (2 : ℚ)) * ((2 : ℚ) / (3 : ℚ))^n + (0 : ℚ) * (-7 : ℚ)^n))

theorem nodes_positive : ∀ q ∈ nodes, 0 < q := by
  intro q hq
  norm_num [nodes] at hq
  rcases hq with rfl | rfl <;> norm_num

theorem nodes_le_one : ∀ q ∈ nodes, q ≤ 1 := by
  intro q hq
  norm_num [nodes] at hq
  rcases hq with rfl | rfl <;> norm_num

theorem weights_positive : ∀ q ∈ nodes, 0 < groupedWeight q := by
  intro q hq
  norm_num [nodes] at hq
  rcases hq with rfl | rfl <;> norm_num [groupedWeight]

theorem mass_one : (∑ q ∈ nodes, groupedWeight q) = 1 := by
  norm_num [nodes, groupedWeight]

/-- All original rows are retained in rawMoment, including exactly zero mass
and distinct spellings of equal rationals. This is one all-exponent identity. -/
theorem grouped_moment_raw (n : ℕ) :
    (∑ q ∈ nodes, groupedWeight q * q^n) = rawMoment n := by
  norm_num [nodes, groupedWeight, rawMoment] <;> ring

noncomputable def law : FinitePositiveLaw :=
  fromGroupedRationals nodes groupedWeight nodes_positive weights_positive mass_one

theorem law_moment_raw (n : ℕ) :
    moment law n = (rawMoment n : ℝ) := by
  calc
    moment law n = ((∑ q ∈ nodes, groupedWeight q * q^n : ℚ) : ℝ) :=
      fromGroupedRationals_moment nodes groupedWeight nodes_positive weights_positive mass_one n
    _ = (rawMoment n : ℝ) := by rw [grouped_moment_raw]

theorem law_nodes_Ioc : ∀ x ∈ law.nodes, 0 < x ∧ x ≤ 1 := by
  intro x hx
  have h := fromGroupedRationals_survival_and_sparse_moments nodes groupedWeight
    nodes_positive nodes_le_one weights_positive mass_one
  exact ⟨law.node_pos x hx, h.1 x hx⟩

theorem sparse_moment_1 : moment law ((1 : ℕ).choose 2) = ((1 : ℚ) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_2 : moment law ((2 : ℕ).choose 2) = (((1 : ℚ) / (2 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_3 : moment law ((3 : ℕ).choose 2) = (((1 : ℚ) / (6 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_4 : moment law ((4 : ℕ).choose 2) = (((65 : ℚ) / (1458 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_5 : moment law ((5 : ℕ).choose 2) = (((1025 : ℚ) / (118098 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]


/-- Literal roots for this supplied mathematical bank. The unchanged certificate
also retains its separate conditional finite_supported_bank theorem. -/
theorem bank_nodes_root : ∀ x ∈ law.nodes, Astra.Generated.Certificate_776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939.polynomial x = 0 := by
  classical
  intro x hx
  change x ∈ nodes.image (fun q : ℚ => (q : ℝ)) at hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
  norm_num [nodes] at hq
  rcases hq with rfl | rfl <;> norm_num [Astra.Generated.Certificate_776e5a30f4a0190153c23bcad5c5d4bddbf2998a6fdcc690f7810eac99134939.polynomial]

end Astra.Generated.BankWitness_4efaf02ca21e032cc08c26d2901d8fe3d11a5d2909894a3c0caea77bffe0c8e8
