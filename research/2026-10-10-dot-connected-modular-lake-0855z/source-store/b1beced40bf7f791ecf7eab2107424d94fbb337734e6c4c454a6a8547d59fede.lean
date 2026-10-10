import ExpandedCorruptionClosure
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Monoid

/-!
CLOUD-G6-SOL-ULTRA-20261007. Compiler UNCHECKED; outside active179.
Construct the actual finite iid sampling law and transfer bounded-test
expectations through closure. This is a fixed-read obstruction, not a
sequential stopping theorem, confidence algorithm or biological admission.
-/
namespace UnifiedLean.G6.FiniteReadClosureObstruction

open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.FiniteCorruptionBoundary
open UnifiedLean.G6.CorruptionClasses UnifiedLean.G6.FiniteSimplexAttainment
open UnifiedLean.G6.CoordinateTVClosure UnifiedLean.G6.ExpandedCorruptionClosure
open scoped BigOperators Classical
variable {A : Type*} [Fintype A]

noncomputable def iidCoordinates (p : PMF A) (n : ℕ) (word : Fin n → A) : ℝ :=
  ∏ i, (p (word i)).toReal

theorem iidCoordinates_nonneg (p : PMF A) (n : ℕ) (word : Fin n → A) :
    0 ≤ iidCoordinates p n word :=
  Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)

theorem iidCoordinates_sum (p : PMF A) (n : ℕ) :
    (∑ word : Fin n → A, iidCoordinates p n word) = 1 := by
  unfold iidCoordinates
  rw [← Fintype.sum_pow, pmf_sum_real]
  simp

/-- Actual n independent repetitions of one fixed observed law. -/
noncomputable def iidPMF (p : PMF A) (n : ℕ) : PMF (Fin n → A) :=
  coordinatePMF (iidCoordinates p n)
    ⟨iidCoordinates_nonneg p n, iidCoordinates_sum p n⟩

theorem iidPMF_real (p : PMF A) (n : ℕ) (word : Fin n → A) :
    (iidPMF p n word).toReal = iidCoordinates p n word := by
  unfold iidPMF
  exact coordinatePMF_real _ _ word

noncomputable def testPolynomial (n : ℕ) (decision : (Fin n → A) → ℝ) (v : A → ℝ) : ℝ :=
  ∑ word : Fin n → A, (∏ i, v (word i)) * decision word

noncomputable def expectedTest (p : PMF A) (n : ℕ) (decision : (Fin n → A) → ℝ) : ℝ :=
  ∑ word : Fin n → A, (iidPMF p n word).toReal * decision word

theorem expectedTest_eq_polynomial (p : PMF A) (n : ℕ)
    (decision : (Fin n → A) → ℝ) :
    expectedTest p n decision = testPolynomial n decision (realLaw p) := by
  simp only [expectedTest, testPolynomial, iidPMF_real, iidCoordinates, realLaw]

theorem continuous_testPolynomial (n : ℕ) (decision : (Fin n → A) → ℝ) :
    Continuous (testPolynomial n decision) := by
  unfold testPolynomial
  apply continuous_finsetSum Finset.univ
  intro word _
  exact (continuous_finsetProd Finset.univ
    (fun i _ => continuous_apply (word i))).mul continuous_const

theorem expectedTest_bounds (p : PMF A) (n : ℕ)
    (decision : (Fin n → A) → ℝ)
    (hdecision : ∀ word, 0 ≤ decision word ∧ decision word ≤ 1) :
    0 ≤ expectedTest p n decision ∧ expectedTest p n decision ≤ 1 := by
  unfold expectedTest
  constructor
  · exact Finset.sum_nonneg (fun word _ =>
      mul_nonneg ENNReal.toReal_nonneg (hdecision word).1)
  · have h := Finset.sum_le_sum (fun word (_ : word ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hdecision word).2
        (ENNReal.toReal_nonneg : 0 ≤ (iidPMF p n word).toReal))
    simpa only [mul_one, pmf_sum_real] using h

/-- Every finite randomized decision expectation is continuous in the law.
Uniform soundness on raw wrong laws therefore extends to their closure. -/
theorem test_upper_bound_on_tvClosure (laws : Set (PMF A))
    (n : ℕ) (decision : (Fin n → A) → ℝ) (alpha : ℝ)
    (hraw : ∀ q ∈ laws, expectedTest q n decision ≤ alpha)
    (z : PMF A) (hz : z ∈ tvClosure laws) :
    expectedTest z n decision ≤ alpha := by
  have hclosed : IsClosed {v : A → ℝ | testPolynomial n decision v ≤ alpha} :=
    isClosed_le (continuous_testPolynomial n decision) continuous_const
  have hsubset : realLaw '' laws ⊆
      {v : A → ℝ | testPolynomial n decision v ≤ alpha} := by
    rintro v ⟨q, hq, rfl⟩
    exact (expectedTest_eq_polynomial q n decision) ▸ hraw q hq
  have hcoords : realLaw z ∈ closure (realLaw '' laws) := by
    have h := hz
    rw [tvClosure_eq_coordinateClosedClass] at h
    exact h
  rw [expectedTest_eq_polynomial]
  exact (closure_minimal hsubset hclosed) hcoords

/-- At/below the sharp two-radius boundary, no n-read randomized binary
decision is uniformly correct on every allowed corruption of p and uniformly
sound on every corruption of every actual raw wrong law. Wrong closure is
derived; raw soundness is not silently required only at an unattained limit. -/
theorem no_uniform_finite_test_at_wrong_closure (p : PMF A)
    (laws : Set (PMF A)) (beta alpha : ℝ) (hb : 0 ≤ beta)
    (halpha : 2 * alpha < 1) (n : ℕ)
    (decision : (Fin n → A) → ℝ)
    (_hdecision : ∀ word, 0 ≤ decision word ∧ decision word ≤ 1)
    (hcorrect : ∀ z : PMF A, pmfTV p z ≤ beta →
      1 - alpha ≤ expectedTest z n decision)
    (hsound : ∀ q ∈ expanded laws beta, expectedTest q n decision ≤ alpha)
    (hboundary : ∃ q ∈ tvClosure laws, pmfTV p q ≤ 2 * beta) : False := by
  obtain ⟨q, hq, hpq⟩ := hboundary
  obtain ⟨z, hpz, hqz⟩ := (shared_corruption_iff p q beta).mpr hpq
  have hz : z ∈ tvClosure (expanded laws beta) := by
    rw [closure_expanded_eq_expanded_closure laws beta hb]
    exact ⟨q, hq, hqz⟩
  have hupper := test_upper_bound_on_tvClosure (expanded laws beta) n decision
    alpha hsound z hz
  have hlower := hcorrect z hpz
  linarith

#print axioms iidCoordinates_nonneg
#print axioms iidCoordinates_sum
#print axioms iidPMF_real
#print axioms expectedTest_eq_polynomial
#print axioms continuous_testPolynomial
#print axioms expectedTest_bounds
#print axioms test_upper_bound_on_tvClosure
#print axioms no_uniform_finite_test_at_wrong_closure

end UnifiedLean.G6.FiniteReadClosureObstruction
