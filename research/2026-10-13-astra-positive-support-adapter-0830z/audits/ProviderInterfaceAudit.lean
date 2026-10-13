import AstraPositiveSupport

/-!
Separate final interface audit, not an accepted-source replacement.

The examples below restate the selected definitions and theorem signatures.
They must be compiled against the authenticated owned/external object paths;
their presence in this file is not an execution receipt. The diagnostic output
prints definitions and actual theorem types without printing theorem proof
terms. This audits the selected interface, not every declaration in Mathlib or
byte identity with upstream Lake objects.
-/

set_option autoImplicit false

namespace Astra.ProviderInterfaceAudit

open DotG4.ActualObservableBankCertificate
open DotG4.ActualSparseCertificateExistence
open DotG4.ActualPositiveGridUniqueness
open Astra.PositiveSupportAdapter
open scoped Classical BigOperators

universe u

-- Exact exponent placement and level enumeration, with no new premise.
example (levels : Finset Nat) (c : Nat → ℝ) :
    sparsePolynomial levels c =
      ∑ k ∈ levels, Polynomial.monomial (k.choose 2) (c k) := rfl

example (L : Nat) :
    momentLevels L = Finset.univ.image (fun n : Fin L => n.val + 1) := rfl

-- The endpoint 1 is present; zero and negative roots are excluded.
example (L : Nat) (c : Nat → ℝ) :
    positiveCertificateGrid L c =
      (sparsePolynomial (momentLevels L) c).roots.toFinset.filter
        (fun x => 0 < x ∧ x ≤ 1) := rfl

-- The accepted theorem requires a nonzero polynomial, not a support cap.
example (L : Nat) (c : Nat → ℝ)
    (hp : sparsePolynomial (momentLevels L) c ≠ 0) :
    (positiveCertificateGrid L c).card < L :=
  positiveCertificateGrid_card_lt L c hp

-- Distinct values count once and zero-mass atoms are excluded.
example {A : Type u} [Fintype A] (weight value : A → ℝ) :
    positiveSupportValues weight value =
      (Finset.univ.filter (fun a => 0 < weight a)).image value := rfl

example {A : Type u} [Fintype A]
    (L : Nat) (c : Nat → ℝ) (p : ℝ → ℝ)
    (identity : ∀ x, p x = (sparsePolynomial (momentLevels L) c).eval x)
    (testPoint : ℝ) (nonzero : p testPoint ≠ 0)
    (weight value : A → ℝ)
    (roots : ∀ a, 0 < weight a → p (value a) = 0 ∧ value a ∈ Set.Ioc (0 : ℝ) 1) :
    (positiveSupportValues weight value).card ≤ L - 1 :=
  positive_support_card_le_pred L c p identity testPoint nonzero weight value roots

-- No survival-domain hypothesis is imposed on zero-mass atoms here.
example {A : Type u} [Fintype A]
    (L : Nat) (c : Nat → ℝ) (p : ℝ → ℝ)
    (identity : ∀ x, p x = (sparsePolynomial (momentLevels L) c).eval x)
    (testPoint : ℝ) (nonzero : p testPoint ≠ 0)
    (weight value : A → ℝ) (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < weight a → value a ∈ Set.Ioc (0 : ℝ) 1)
    (nonnegative : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p x)
    (annihilation : ∑ a, weight a * p (value a) = 0) :
    (positiveSupportValues weight value).card ≤ L - 1 :=
  supplied_certificate_support_bound L c p identity testPoint nonzero
    weight value hw hv nonnegative annihilation

example : momentLevels 3 = {1, 2, 3} := threeLevels

example (constant linear cubic : ℝ) (k : Nat) :
    threeCoefficients constant linear cubic k =
      if k = 1 then constant else if k = 2 then linear else if k = 3 then cubic else 0 := rfl

example (constant linear cubic x : ℝ) :
    (sparsePolynomial (momentLevels 3) (threeCoefficients constant linear cubic)).eval x =
      constant + linear * x + cubic * x ^ 3 :=
  threeCoefficients_eval constant linear cubic x

-- The literal examples retain their original all-atom domain assumptions.
example {A : Type u} [Fintype A]
    (weight value : A → ℝ) (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a) ^ 0 = 1)
    (moment1 : ∑ a, weight a * (value a) ^ 1 = (1 / 4 : ℝ))
    (moment3 : ∑ a, weight a * (value a) ^ 3 = (1 / 64 : ℝ)) :
    (positiveSupportValues weight value).card ≤ 2 :=
  quarter_emitted_support_bound weight value hw hv moment0 moment1 moment3

example {A : Type u} [Fintype A]
    (weight value : A → ℝ) (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a) ^ 0 = 1)
    (moment1 : ∑ a, weight a * (value a) ^ 1 = (1 / 2 : ℝ))
    (moment3 : ∑ a, weight a * (value a) ^ 3 = (1 / 8 : ℝ)) :
    (positiveSupportValues weight value).card ≤ 2 :=
  half_emitted_support_bound weight value hw hv moment0 moment1 moment3

example {A : Type u} [Fintype A]
    (weight value : A → ℝ) (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a) ^ 0 = 1)
    (moment1 : ∑ a, weight a * (value a) ^ 1 = (1 : ℝ))
    (moment3 : ∑ a, weight a * (value a) ^ 3 = (1 : ℝ)) :
    (positiveSupportValues weight value).card ≤ 2 :=
  endpoint_emitted_support_bound weight value hw hv moment0 moment1 moment3

end Astra.ProviderInterfaceAudit

-- Explicit parameters, universes, full names and unfolded notation make the
-- actual elaborated interface available for comparison with the source above.
-- #check prints theorem types; #print is limited to the small definitions.
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.notation false
set_option pp.proofs false

#print DotG4.ActualObservableBankCertificate.sparsePolynomial
#print DotG4.ActualSparseCertificateExistence.momentLevels
#print DotG4.ActualPositiveGridUniqueness.positiveCertificateGrid
#print Astra.PositiveSupportAdapter.positiveSupportValues
#print Astra.PositiveSupportAdapter.threeCoefficients

#check @DotG4.ActualPositiveGridUniqueness.positiveCertificateGrid_card_lt
#check @Astra.PositiveSupportAdapter.positive_support_card_le_pred
#check @Astra.PositiveSupportAdapter.supplied_certificate_support_bound
#check @Astra.PositiveSupportAdapter.threeLevels
#check @Astra.PositiveSupportAdapter.threeCoefficients_eval
#check @Astra.PositiveSupportAdapter.quarter_emitted_support_bound
#check @Astra.PositiveSupportAdapter.half_emitted_support_bound
#check @Astra.PositiveSupportAdapter.endpoint_emitted_support_bound

#print axioms DotG4.ActualPositiveGridUniqueness.positiveCertificateGrid_card_lt
#print axioms Astra.PositiveSupportAdapter.positive_support_card_le_pred
#print axioms Astra.PositiveSupportAdapter.supplied_certificate_support_bound
#print axioms Astra.PositiveSupportAdapter.threeLevels
#print axioms Astra.PositiveSupportAdapter.threeCoefficients_eval
#print axioms Astra.PositiveSupportAdapter.quarter_emitted_support_bound
#print axioms Astra.PositiveSupportAdapter.half_emitted_support_bound
#print axioms Astra.PositiveSupportAdapter.endpoint_emitted_support_bound
