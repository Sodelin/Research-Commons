import Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60
import Astra.PositiveSupportAdapter

/- Exact certificate identity: 7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60.
Conditional distinct positive-mass values only; generation is not compilation. -/
namespace Astra.GeneratedSupport.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60
open Astra.Generated.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60
open Astra.PositiveSupportAdapter
open DotG4.ActualObservableBankCertificate
open DotG4.ActualSparseCertificateExistence
open scoped BigOperators

noncomputable def coefficients (k : Nat) : ℝ := if k = 1 then ((0 : ℝ) / 1) else if k = 2 then ((0 : ℝ) / 1) else if k = 3 then ((0 : ℝ) / 1) else if k = 4 then ((0 : ℝ) / 1) else if k = 5 then ((0 : ℝ) / 1) else if k = 6 then ((0 : ℝ) / 1) else if k = 7 then ((0 : ℝ) / 1) else if k = 8 then ((1 : ℝ) / 1) else 0

lemma levels_eq : momentLevels 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by
  ext k
  simp only [momentLevels, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    have hn := n.isLt
    omega
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · subst k
      exact ⟨⟨0, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨1, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨2, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨3, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨4, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨5, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨6, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨7, by decide⟩, rfl⟩

theorem polynomial_identity (x : ℝ) :
    polynomial x = (sparsePolynomial (momentLevels 8) coefficients).eval x := by
  rw [sparsePolynomial_eval, levels_eq]
  norm_num [coefficients, polynomial]

theorem distinct_positive_support_bound {A : Type*} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((0 : ℝ) / 1))
    (moment2 : ∑ a, weight a * (value a)^3 = ((0 : ℝ) / 1))
    (moment3 : ∑ a, weight a * (value a)^6 = ((0 : ℝ) / 1))
    (moment4 : ∑ a, weight a * (value a)^10 = ((0 : ℝ) / 1))
    (moment5 : ∑ a, weight a * (value a)^15 = ((0 : ℝ) / 1))
    (moment6 : ∑ a, weight a * (value a)^21 = ((0 : ℝ) / 1))
    (moment7 : ∑ a, weight a * (value a)^28 = ((0 : ℝ) / 1))
    : (positiveSupportValues weight value).card ≤ 7 := by
  apply positive_support_card_le_pred 8 coefficients polynomial polynomial_identity 1 nonzero_value weight value
  intro a ha
  exact finite_supported_bank weight value hw hv moment0 moment1 moment2 moment3 moment4 moment5 moment6 moment7 a ha

#print axioms levels_eq
#print axioms polynomial_identity
#print axioms distinct_positive_support_bound
end Astra.GeneratedSupport.Certificate_7319029dcb55d6e9cbd4b960ac39371a113ab84187ef57a3bfcc55bbc0314b60
