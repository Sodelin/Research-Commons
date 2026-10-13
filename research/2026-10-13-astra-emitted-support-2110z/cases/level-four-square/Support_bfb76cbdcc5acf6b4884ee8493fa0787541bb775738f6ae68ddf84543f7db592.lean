import Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592
import Astra.PositiveSupportAdapter

/- Exact certificate identity: bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592.
Conditional distinct positive-mass values only; generation is not compilation. -/
namespace Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592
open Astra.Generated.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592
open Astra.PositiveSupportAdapter
open DotG4.ActualObservableBankCertificate
open DotG4.ActualSparseCertificateExistence
open scoped BigOperators

noncomputable def coefficients (k : Nat) : ℝ := if k = 1 then ((1 : ℝ) / 64) else if k = 2 then ((0 : ℝ) / 1) else if k = 3 then ((-1 : ℝ) / 4) else if k = 4 then ((1 : ℝ) / 1) else 0

lemma levels_eq : momentLevels 4 = {1, 2, 3, 4} := by
  ext k
  simp only [momentLevels, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    have hn := n.isLt
    omega
  · intro h
    rcases h with h | h | h | h
    · subst k
      exact ⟨⟨0, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨1, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨2, by decide⟩, rfl⟩
    · subst k
      exact ⟨⟨3, by decide⟩, rfl⟩

theorem polynomial_identity (x : ℝ) :
    polynomial x = (sparsePolynomial (momentLevels 4) coefficients).eval x := by
  rw [sparsePolynomial_eval, levels_eq]
  norm_num [coefficients, polynomial]

theorem distinct_positive_support_bound {A : Type*} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 2))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 8))
    (moment3 : ∑ a, weight a * (value a)^6 = ((1 : ℝ) / 64))
    : (positiveSupportValues weight value).card ≤ 3 := by
  apply positive_support_card_le_pred 4 coefficients polynomial polynomial_identity 0 nonzero_value weight value
  intro a ha
  exact finite_supported_bank weight value hw hv moment0 moment1 moment2 moment3 a ha

#print axioms levels_eq
#print axioms polynomial_identity
#print axioms distinct_positive_support_bound
end Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592
