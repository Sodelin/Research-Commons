import G4ActualPositiveGridUniqueness
import Astra.CommonCertificateKernel

/-!
Conditional distinct positive-support adapter. The accepted provider is imported
with its complete selected body and dependencies. No physical representative,
source existence, graph bound or arbitrary-input G3 decision follows.
-/
namespace Astra.PositiveSupportAdapter

open DotG4.ActualObservableBankCertificate
open DotG4.ActualSparseCertificateExistence
open DotG4.ActualPositiveGridUniqueness
open scoped Classical BigOperators

/-- Distinct values of positive-mass atoms. Repeated values count once;
zero-mass atoms do not enter the set, regardless of their assigned values. -/
noncomputable def positiveSupportValues {A : Type*} [Fintype A]
    (weight value : A → ℝ) : Finset ℝ :=
  (Finset.univ.filter (fun a => 0 < weight a)).image value

/-- The binding is an exact polynomial evaluation identity. Nonzeroness comes
from a concrete nonzero evaluation, and roots come from the supplied certificate
consequence. The requested cardinality conclusion is not an input. -/
theorem positive_support_card_le_pred {A : Type*} [Fintype A]
    (L : Nat) (c : Nat → ℝ) (p : ℝ → ℝ)
    (identity : ∀ x, p x = (sparsePolynomial (momentLevels L) c).eval x)
    (testPoint : ℝ) (nonzero : p testPoint ≠ 0)
    (weight value : A → ℝ)
    (roots : ∀ a, 0 < weight a → p (value a) = 0 ∧ value a ∈ Set.Ioc (0 : ℝ) 1) :
    (positiveSupportValues weight value).card ≤ L - 1 := by
  have hp : sparsePolynomial (momentLevels L) c ≠ 0 := by
    intro hz
    apply nonzero
    rw [identity, hz, Polynomial.eval_zero]
  have hsubset : positiveSupportValues weight value ⊆ positiveCertificateGrid L c := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have hpositive : 0 < weight a := (Finset.mem_filter.mp ha).2
    have hroot := roots a hpositive
    apply Finset.mem_filter.mpr
    refine ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr ?_), hroot.2⟩
    change (sparsePolynomial (momentLevels L) c).eval (value a) = 0
    rw [← identity]
    exact hroot.1
  have hlt := (Finset.card_le_card hsubset).trans_lt (positiveCertificateGrid_card_lt L c hp)
  omega

/-- A direct supplied-certificate consequence. Zero-weight atoms need neither
a survival-domain hypothesis nor a root assertion. Survival endpoint 1 is kept. -/
theorem supplied_certificate_support_bound {A : Type*} [Fintype A]
    (L : Nat) (c : Nat → ℝ) (p : ℝ → ℝ)
    (identity : ∀ x, p x = (sparsePolynomial (momentLevels L) c).eval x)
    (testPoint : ℝ) (nonzero : p testPoint ≠ 0)
    (weight value : A → ℝ) (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < weight a → value a ∈ Set.Ioc (0 : ℝ) 1)
    (nonnegative : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p x)
    (annihilation : ∑ a, weight a * p (value a) = 0) :
    (positiveSupportValues weight value).card ≤ L - 1 := by
  apply positive_support_card_le_pred L c p identity testPoint nonzero weight value
  have terms : ∀ a, 0 ≤ weight a * p (value a) := by
    intro a
    by_cases hz : weight a = 0
    · simp [hz]
    · have hpositive : 0 < weight a := lt_of_le_of_ne (hw a) (Ne.symm hz)
      have domain := hv a hpositive
      exact mul_nonneg (hw a) (nonnegative (value a) ⟨domain.1.le, domain.2⟩)
  have each := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a (_ : a ∈ (Finset.univ : Finset A)) => terms a)).mp annihilation
  intro a ha
  exact ⟨(mul_eq_zero.mp (each a (Finset.mem_univ a))).resolve_left (ne_of_gt ha), hv a ha⟩

/-- Literal coefficient placement for the emitted levels 1,2,3, whose exact
exponents are respectively 0,1,3. Coefficients outside these levels are zero. -/
noncomputable def threeCoefficients (constant linear cubic : ℝ) (k : Nat) : ℝ :=
  if k = 1 then constant else if k = 2 then linear else if k = 3 then cubic else 0

lemma threeLevels : momentLevels 3 = {1, 2, 3} := by
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

lemma threeCoefficients_eval (constant linear cubic x : ℝ) :
    (sparsePolynomial (momentLevels 3) (threeCoefficients constant linear cubic)).eval x =
      constant + linear * x + cubic * x^3 := by
  rw [sparsePolynomial_eval, threeLevels]
  norm_num [threeCoefficients]

#print axioms positive_support_card_le_pred
#print axioms supplied_certificate_support_bound
#print axioms threeLevels
#print axioms threeCoefficients_eval

end Astra.PositiveSupportAdapter
