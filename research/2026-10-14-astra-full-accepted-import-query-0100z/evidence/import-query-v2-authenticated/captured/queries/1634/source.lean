import Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4
import Astra.PositiveSupportAdapter

/- Exact certificate identity: 185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4.
Conditional distinct positive-mass values only; generation is not compilation. -/
namespace Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4
open Astra.Generated.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4
open Astra.PositiveSupportAdapter
open DotG4.ActualObservableBankCertificate
open DotG4.ActualSparseCertificateExistence
open scoped BigOperators

noncomputable def coefficients (k : Nat) : ℝ := if k = 1 then ((1 : ℝ) / 1) else if k = 2 then ((-1 : ℝ) / 1) else 0

lemma levels_eq : momentLevels 2 = {1, 2} := by
  ext k
  simp only [momentLevels, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    have hn := n.isLt
    omega
  · intro h
    rcases h with h | h
    · subst k
      exact ⟨⟨0, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨1, by decide⟩, rfl⟩

theorem polynomial_identity (x : ℝ) :
    polynomial x = (sparsePolynomial (momentLevels 2) coefficients).eval x := by
  rw [sparsePolynomial_eval, levels_eq]
  norm_num [coefficients, polynomial]

theorem distinct_positive_support_bound {A : Type*} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 1))
    : (positiveSupportValues weight value).card ≤ 1 := by
  apply positive_support_card_le_pred 2 coefficients polynomial polynomial_identity 0 nonzero_value weight value
  intro a ha
  exact finite_supported_bank weight value hw hv moment0 moment1 a ha

#print axioms levels_eq
#print axioms polynomial_identity
#print axioms distinct_positive_support_bound
end Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4
