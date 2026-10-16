import Semi.Statistics.FiniteDecision
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormCast

/-!
UNCOMPILED SOURCE CANDIDATE. Contributor: dot (OpenAI), 2026-10-16.
Supplier: FiniteDecision at edd37b2bb838baf71b1e8d908da1a47c409834f1,
selected module Semi.Statistics.FiniteDecision in certificate 3d16602f.
No new source-admission or registry-completeness assertion is made here.
-/

namespace Semi.Statistics.FiniteSupport

open Finset

variable {X O A I : Type*} [Fintype A] [Nonempty A]
  [Fintype I] [Nonempty I]

/-- Both sums are finite; the source type X is arbitrary. -/
theorem weighted_risk_identity (loss : A → X → ℝ)
    (q : RandomizedAction A) (w : RandomizedAction I) (s : I → X) :
    (∑ i, w i * risk loss q (s i)) =
      ∑ a, q a * (∑ i, w i * loss a (s i)) := by
  classical
  calc
    (∑ i, w i * risk loss q (s i)) =
        ∑ i, ∑ a, w i * (q a * loss a (s i)) := by
          simp only [risk, Finset.mul_sum]
    _ = ∑ a, ∑ i, w i * (q a * loss a (s i)) := Finset.sum_comm
    _ = ∑ a, q a * (∑ i, w i * loss a (s i)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A supplied dual inequality bounds every randomized action on the full A. -/
theorem weighted_risk_lower_bound (loss : A → X → ℝ)
    (q : RandomizedAction A) (w : RandomizedAction I) (s : I → X)
    (l : ℝ) (dual : ∀ a, l ≤ ∑ i, w i * loss a (s i)) :
    l ≤ ∑ i, w i * risk loss q (s i) := by
  classical
  rw [weighted_risk_identity]
  calc
    l = ∑ a, q a * l := by
      rw [← Finset.sum_mul, stdSimplex.sum_eq_one q, one_mul]
    _ ≤ ∑ a, q a * (∑ i, w i * loss a (s i)) :=
      Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (dual a) (stdSimplex.zero_le q a)

theorem weighted_risk_le_of_pointwise (loss : A → X → ℝ)
    (q : RandomizedAction A) (w : RandomizedAction I) (s : I → X)
    (u : ℝ) (upper : ∀ i, risk loss q (s i) ≤ u) :
    (∑ i, w i * risk loss q (s i)) ≤ u := by
  classical
  calc
    (∑ i, w i * risk loss q (s i)) ≤ ∑ i, w i * u :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (upper i) (stdSimplex.zero_le w i)
    _ = u := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one w, one_mul]

/-- Finite support suffices; no Fintype X or coverage of X is needed. -/
theorem support_max_lower_bound (loss : A → X → ℝ)
    (q : RandomizedAction A) (w : RandomizedAction I) (s : I → X)
    (l : ℝ) (dual : ∀ a, l ≤ ∑ i, w i * loss a (s i)) :
    l ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => risk loss q (s i)) := by
  classical
  exact (weighted_risk_lower_bound loss q w s l dual).trans
    (weighted_risk_le_of_pointwise loss q w s _
      (fun i => Finset.le_sup' _ (Finset.mem_univ i)))

/-- The same observation and the same rule yield the common decision q. -/
theorem same_observation_support_lower_bound (observe : X → O)
    (loss : A → X → ℝ) (rule : DecisionRule O A) (o : O)
    (w : RandomizedAction I) (s : I → X) (same : ∀ i, observe (s i) = o)
    (l : ℝ) (dual : ∀ a, l ≤ ∑ i, w i * loss a (s i)) :
    l ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun i => risk loss (rule (observe (s i))) (s i)) := by
  classical
  simpa only [same] using support_max_lower_bound loss (rule o) w s l dual

/-- Exact rational table values and weights coerce to the real dual inequality.
The action index is the entire A, not a smaller list of selected actions. -/
theorem dual_of_exact_rational_table (loss : A → X → ℝ)
    (w : RandomizedAction I) (s : I → X) (L : A → I → ℚ)
    (v : I → ℚ) (l : ℚ)
    (weights : ∀ i, w i = (v i : ℝ))
    (binding : ∀ a i, (L a i : ℝ) = loss a (s i))
    (dual : ∀ a, l ≤ ∑ i, v i * L a i) :
    ∀ a, (l : ℝ) ≤ ∑ i, w i * loss a (s i) := by
  intro a
  have h : (l : ℝ) ≤ ∑ i, (v i : ℝ) * (L a i : ℝ) := by
    exact_mod_cast dual a
  simpa only [weights, binding] using h

/-- A checked rational primal row yields its real expected-risk bound. -/
theorem upper_of_exact_rational_table (loss : A → X → ℝ)
    (q : RandomizedAction A) (s : I → X) (L : A → I → ℚ)
    (v : A → ℚ) (u : ℚ)
    (weights : ∀ a, q a = (v a : ℝ))
    (binding : ∀ a i, (L a i : ℝ) = loss a (s i))
    (rows : ∀ i, (∑ a, v a * L a i) ≤ u) :
    ∀ i, risk loss q (s i) ≤ (u : ℝ) := by
  intro i
  have h : (∑ a, (v a : ℝ) * (L a i : ℝ)) ≤ (u : ℝ) := by
    exact_mod_cast rows i
  simpa only [risk, weights, binding] using h

section FiniteFibre
variable [Fintype X]

/-- Only membership, not coverage, is needed for a lower certificate. -/
theorem fibreMinimaxRadius_support_lower_bound (observe : X → O)
    (loss : A → X → ℝ) (o : Set.range observe)
    (w : RandomizedAction I) (s : I → X)
    (admitted : ∀ i, observe (s i) = o.1)
    (l : ℝ) (dual : ∀ a, l ≤ ∑ i, w i * loss a (s i)) :
    l ≤ fibreMinimaxRadius observe loss o := by
  classical
  let q := fibreMinimizer observe loss o
  have lower := weighted_risk_lower_bound loss q w s l dual
  have upper : ∀ i, risk loss q (s i) ≤ fibreWorstRisk observe loss o q := by
    intro i
    have hi : s i ∈ fibreStates observe o.1 := by
      simp [fibreStates, admitted i]
    exact Finset.le_sup' _ hi
  change l ≤ fibreWorstRisk observe loss o q
  exact lower.trans (weighted_risk_le_of_pointwise loss q w s _ upper)

/-- Upper certificates require coverage of the entire observation fibre.
This premise is an explicit application obligation, not an admission procedure. -/
theorem fibreMinimaxRadius_upper_of_coverage (observe : X → O)
    (loss : A → X → ℝ) (o : Set.range observe)
    (q : RandomizedAction A) (s : I → X)
    (covers : ∀ x, observe x = o.1 → ∃ i, s i = x)
    (u : ℝ) (upper : ∀ i, risk loss q (s i) ≤ u) :
    fibreMinimaxRadius observe loss o ≤ u := by
  classical
  apply (fibreMinimaxRadius_le observe loss o q).trans
  apply (Finset.sup'_le_iff (fibreStates_nonempty observe o) _).2
  intro x hx
  have hobs : observe x = o.1 := by simpa [fibreStates] using hx
  obtain ⟨i, hi⟩ := covers x hobs
  simpa only [hi] using upper i

end FiniteFibre
end Semi.Statistics.FiniteSupport
