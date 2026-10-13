import Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766
import Astra.PositiveSupportAdapter

/- Exact certificate identity: fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766.
Conditional distinct positive-mass values only; generation is not compilation. -/
namespace Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766
open Astra.Generated.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766
open Astra.PositiveSupportAdapter
open DotG4.ActualObservableBankCertificate
open DotG4.ActualSparseCertificateExistence
open scoped BigOperators

noncomputable def coefficients (k : Nat) : ℝ := if k = 1 then ((0 : ℝ) / 1) else if k = 2 then ((1 : ℝ) / 1) else if k = 3 then ((-1 : ℝ) / 1) else 0

lemma levels_eq : momentLevels 3 = {1, 2, 3} := by
  ext k
  simp only [momentLevels, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    have hn := n.isLt
    omega
  · intro h
    rcases h with h | h | h
    · subst k
      exact ⟨⟨0, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨1, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨2, by decide⟩, rfl⟩

theorem polynomial_identity (x : ℝ) :
    polynomial x = (sparsePolynomial (momentLevels 3) coefficients).eval x := by
  rw [sparsePolynomial_eval, levels_eq]
  norm_num [coefficients, polynomial]

theorem distinct_positive_support_bound {A : Type*} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 1))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 1))
    : (positiveSupportValues weight value).card ≤ 2 := by
  apply positive_support_card_le_pred 3 coefficients polynomial polynomial_identity 2 nonzero_value weight value
  intro a ha
  exact finite_supported_bank weight value hw hv moment0 moment1 moment2 a ha

#print axioms levels_eq
#print axioms polynomial_identity
#print axioms distinct_positive_support_bound
end Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766
