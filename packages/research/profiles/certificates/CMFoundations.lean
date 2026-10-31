import CMSparseSupplier
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
COMMON-MOMENT-HAND-001-v1: first disjoint lane2 SOURCE CANDIDATE.
UNCOMPILED AND UNEXECUTED. No CM-T02 endpoint or physical compiler binding
is claimed. Reuses the existing sparse-certificate module and Mathlib rule
of signs; no new axiom, opaque certificate assumption or placeholder proof.
-/

namespace Astra.CommonMoment

open Polynomial
open scoped BigOperators

/-- Positive-axis laws for CM-T02; CM-T01 additionally requires nodes below one. -/
structure FinitePositiveLaw where
  nodes : Finset ℝ
  weight : ℝ → ℝ
  node_pos : ∀ x ∈ nodes, 0 < x
  weight_pos : ∀ x ∈ nodes, 0 < weight x
  mass_one : (∑ x ∈ nodes, weight x) = 1

noncomputable def moment (μ : FinitePositiveLaw) (k : ℕ) : ℝ :=
  ∑ x ∈ μ.nodes, μ.weight x * x ^ k

def StrictlyInterior (μ : FinitePositiveLaw) : Prop :=
  ∀ x ∈ μ.nodes, x < 1

theorem moment_zero (μ : FinitePositiveLaw) : moment μ 0 = 1 := by
  simpa [moment] using μ.mass_one

/-- CM-L01, via the already selected Descartes and sparse-support suppliers.
Polynomial.roots is a multiset, so this count includes multiplicities. -/
theorem positive_root_count_lt_support_card (P : ℝ[X]) (hP : P ≠ 0) :
    P.roots.countP (0 < ·) < P.support.card := by
  exact lt_of_le_of_lt P.roots_countP_pos_le_signVariations
    (DotG4.ActualSparseCertificateExistence.signVariations_lt_support_card P hP)

theorem cm_l01_positive_root_bound (P : ℝ[X]) (hP : P ≠ 0)
    (r : ℕ) (hs : P.support.card ≤ r) :
    P.roots.countP (0 < ·) ≤ r - 1 := by
  have h := positive_root_count_lt_support_card P hP
  omega

/-- The singleton competitor repair uses only exponents zero, one and three. -/
def singletonPolynomial (a x : ℝ) : ℝ :=
  (x - a) ^ 2 * (x + 2 * a)

theorem singletonPolynomial_expansion (a x : ℝ) :
    singletonPolynomial a x = x ^ 3 - 3 * a ^ 2 * x + 2 * a ^ 3 := by
  unfold singletonPolynomial
  ring

theorem singletonPolynomial_at_node (a : ℝ) :
    singletonPolynomial a a = 0 := by
  simp [singletonPolynomial]

theorem singletonPolynomial_nonneg {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 ≤ singletonPolynomial a x := by
  unfold singletonPolynomial
  exact mul_nonneg (sq_nonneg _) (by linarith)

theorem singletonPolynomial_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxa : x ≠ a) : 0 < singletonPolynomial a x := by
  unfold singletonPolynomial
  have hs : 0 < (x - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxa)
  exact mul_pos hs (by linarith)

theorem three_products_strict {a b c d : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hab : a < b) (hcd : c < d) :
    a * c < a * d ∧ a * d < b * d := by
  exact ⟨mul_lt_mul_of_pos_left hcd ha, mul_lt_mul_of_pos_right hab hd⟩

end Astra.CommonMoment
