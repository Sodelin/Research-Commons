import CMRationalBank
import Astra.Generated.Certificate_e49c1e3d6bffee594b99574d3364e700e8f25342933fe31add2aa6129729bc6b
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Astra.Generated.BankWitness_d71c2bf0e0153f8103feb7a65084e462c4b20ea5bc823ace0312057491697979

open scoped BigOperators
open Astra.CommonMoment
open Astra.CommonMoment.RationalBank

def nodes : Finset ℚ := {((1 : ℚ) / (4 : ℚ)), ((1 : ℚ) / (2 : ℚ)), ((3 : ℚ) / (4 : ℚ))}

def groupedWeight (q : ℚ) : ℚ :=
  if q = ((1 : ℚ) / (4 : ℚ)) then ((1 : ℚ) / (3 : ℚ)) else if q = ((1 : ℚ) / (2 : ℚ)) then ((1 : ℚ) / (3 : ℚ)) else if q = ((3 : ℚ) / (4 : ℚ)) then ((1 : ℚ) / (3 : ℚ)) else (0 : ℚ)

def rawMoment (n : ℕ) : ℚ :=
  (((1 : ℚ) / (3 : ℚ)) * ((1 : ℚ) / (4 : ℚ))^n + (((1 : ℚ) / (3 : ℚ)) * ((1 : ℚ) / (2 : ℚ))^n + ((1 : ℚ) / (3 : ℚ)) * ((3 : ℚ) / (4 : ℚ))^n))

theorem nodes_positive : ∀ q ∈ nodes, 0 < q := by
  intro q hq
  norm_num [nodes] at hq
  rcases hq with rfl | rfl | rfl <;> norm_num

theorem nodes_le_one : ∀ q ∈ nodes, q ≤ 1 := by
  intro q hq
  norm_num [nodes] at hq
  rcases hq with rfl | rfl | rfl <;> norm_num

theorem weights_positive : ∀ q ∈ nodes, 0 < groupedWeight q := by
  intro q hq
  norm_num [nodes] at hq
  rcases hq with rfl | rfl | rfl <;> norm_num [groupedWeight]

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

theorem sparse_moment_3 : moment law ((3 : ℕ).choose 2) = (((3 : ℚ) / (16 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_4 : moment law ((4 : ℕ).choose 2) = (((397 : ℚ) / (6144 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_5 : moment law ((5 : ℕ).choose 2) = (((30037 : ℚ) / (1572864 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_6 : moment law ((6 : ℕ).choose 2) = (((1198473 : ℚ) / (268435456 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]

theorem sparse_moment_7 : moment law ((7 : ℕ).choose 2) = (((871870863 : ℚ) / (1099511627776 : ℚ)) : ℝ) := by
  rw [law_moment_raw]
  norm_num [rawMoment, Nat.choose]


/-- Literal roots for this supplied mathematical bank. The unchanged certificate
also retains its separate conditional finite_supported_bank theorem. -/
theorem bank_nodes_root : ∀ x ∈ law.nodes, Astra.Generated.Certificate_e49c1e3d6bffee594b99574d3364e700e8f25342933fe31add2aa6129729bc6b.polynomial x = 0 := by
  classical
  intro x hx
  change x ∈ nodes.image (fun q : ℚ => (q : ℝ)) at hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
  norm_num [nodes] at hq
  rcases hq with rfl | rfl | rfl <;> norm_num [Astra.Generated.Certificate_e49c1e3d6bffee594b99574d3364e700e8f25342933fe31add2aa6129729bc6b.polynomial]

end Astra.Generated.BankWitness_d71c2bf0e0153f8103feb7a65084e462c4b20ea5bc823ace0312057491697979
