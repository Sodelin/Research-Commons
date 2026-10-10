import FiniteReadClosureObstruction
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026. Compiler UNCHECKED;
outside the sole181 selection. Countable finite-prefix acceptance bounds.
This proves an operational supremum obstruction, not the missing general
infinite-product/random-seed/stopping-time measurability bridge.
-/
namespace UnifiedLean.G6.SequentialPrefixClosureObstruction

open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.FiniteCorruptionBoundary
open UnifiedLean.G6.CorruptionClasses UnifiedLean.G6.ExpandedCorruptionClosure
open UnifiedLean.G6.FiniteReadClosureObstruction
open scoped BigOperators Classical
variable {A : Type*} [Fintype A]

/-- One fixed observer's finite-prefix randomized positive-decision weights.
Coefficients depend only on the finite observed word, never its source law.
Coherence is not needed by the obstruction, which therefore covers every
coherent stopping rule after its finite-prefix acceptance weights are given. -/
abbrev PrefixDecisions (A : Type*) := (n : ℕ) → (Fin n → A) → ℝ

noncomputable def eventualAcceptance (p : PMF A) (decision : PrefixDecisions A) : ℝ :=
  sSup (Set.range (fun n => expectedTest p n (decision n)))

theorem prefix_acceptance_bddAbove (p : PMF A) (decision : PrefixDecisions A)
    (hd : ∀ n word, 0 ≤ decision n word ∧ decision n word ≤ 1) :
    BddAbove (Set.range (fun n => expectedTest p n (decision n))) := by
  refine ⟨1, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (expectedTest_bounds p n (decision n) (hd n)).2

theorem prefix_acceptance_le_eventual (p : PMF A) (decision : PrefixDecisions A)
    (hd : ∀ n word, 0 ≤ decision n word ∧ decision n word ≤ 1) (n : ℕ) :
    expectedTest p n (decision n) ≤ eventualAcceptance p decision := by
  exact le_csSup (prefix_acceptance_bddAbove p decision hd) (Set.mem_range_self n)

theorem eventualAcceptance_bounds (p : PMF A) (decision : PrefixDecisions A)
    (hd : ∀ n word, 0 ≤ decision n word ∧ decision n word ≤ 1) :
    0 ≤ eventualAcceptance p decision ∧ eventualAcceptance p decision ≤ 1 := by
  constructor
  · exact le_trans (expectedTest_bounds p 0 (decision 0) (hd 0)).1
      (prefix_acceptance_le_eventual p decision hd 0)
  · apply csSup_le (Set.range_nonempty _)
    rintro x ⟨n, rfl⟩
    exact (expectedTest_bounds p n (decision n) (hd n)).2

/-- Uniform eventual upper bounds on the raw wrong set extend to its TV
closure: each finite polynomial is bounded there, then their supremum is.
No common deterministic or expected read-count bound is assumed. -/
theorem eventual_upper_bound_on_tvClosure (laws : Set (PMF A))
    (decision : PrefixDecisions A) (alpha : ℝ)
    (hd : ∀ n word, 0 ≤ decision n word ∧ decision n word ≤ 1)
    (hraw : ∀ q ∈ laws, eventualAcceptance q decision ≤ alpha)
    (z : PMF A) (hz : z ∈ tvClosure laws) :
    eventualAcceptance z decision ≤ alpha := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨n, rfl⟩
  apply test_upper_bound_on_tvClosure laws n (decision n) alpha ?_ z hz
  intro q hq
  exact le_trans (prefix_acceptance_le_eventual q decision hd n) (hraw q hq)

/-- The same observer cannot achieve the two uniform eventual acceptance
bounds at or below the sharp two-radius wrong-closure boundary, even with
unbounded numbers of reads. Supremum semantics and all raw wrong laws are
explicit; this is not an effective or statistical recovery algorithm. -/
theorem no_uniform_prefix_stopping_at_wrong_closure (p : PMF A)
    (laws : Set (PMF A)) (beta alpha : ℝ) (hb : 0 ≤ beta)
    (halpha : 2 * alpha < 1) (decision : PrefixDecisions A)
    (hd : ∀ n word, 0 ≤ decision n word ∧ decision n word ≤ 1)
    (hcorrect : ∀ z : PMF A, pmfTV p z ≤ beta →
      1 - alpha ≤ eventualAcceptance z decision)
    (hsound : ∀ q ∈ expanded laws beta,
      eventualAcceptance q decision ≤ alpha)
    (hboundary : ∃ q ∈ tvClosure laws, pmfTV p q ≤ 2 * beta) : False := by
  obtain ⟨q, hq, hpq⟩ := hboundary
  obtain ⟨z, hpz, hqz⟩ := (shared_corruption_iff p q beta).mpr hpq
  have hz : z ∈ tvClosure (expanded laws beta) := by
    rw [closure_expanded_eq_expanded_closure laws beta hb]
    exact ⟨q, hq, hqz⟩
  have hupper := eventual_upper_bound_on_tvClosure (expanded laws beta)
    decision alpha hd hsound z hz
  have hlower := hcorrect z hpz
  linarith

inductive StopSignal where
  | keepReading
  | positive
  | negative
  deriving DecidableEq

/-- A prefix interpreter with an independent once-drawn finite seed.
Arbitrary unbounded memory is represented by the entire word argument. -/
abbrev StoppingRule (Seed A : Type*) := Seed → (n : ℕ) → (Fin n → A) → StopSignal

def firstPositiveBy {Seed : Type*} (rule : StoppingRule Seed A)
    (seed : Seed) (n : ℕ) (word : Fin n → A) : Prop :=
  ∃ k, ∃ hk : k ≤ n,
    rule seed k (fun i => word (Fin.castLE hk i)) = StopSignal.positive ∧
    ∀ j, ∀ hj : j < k,
      rule seed j (fun i => word (Fin.castLE (le_trans (Nat.le_of_lt hj) hk) i)) =
        StopSignal.keepReading

theorem firstPositiveBy_prefix_mono {Seed : Type*} (rule : StoppingRule Seed A)
    (seed : Seed) {m n : ℕ} (hmn : m ≤ n) (word : Fin n → A)
    (h : firstPositiveBy rule seed m (fun i => word (Fin.castLE hmn i))) :
    firstPositiveBy rule seed n word := by
  obtain ⟨k, hk, hp, hc⟩ := h
  refine ⟨k, le_trans hk hmn, ?_, ?_⟩
  · simpa only [Fin.castLE_castLE] using hp
  · intro j hj
    simpa only [Fin.castLE_castLE] using hc j hj

noncomputable def stoppingPrefixDecision {Seed : Type*} [Fintype Seed]
    (seedLaw : PMF Seed) (rule : StoppingRule Seed A)
    (n : ℕ) (word : Fin n → A) : ℝ :=
  ∑ seed : Seed, (seedLaw seed).toReal *
    (if firstPositiveBy rule seed n word then 1 else 0)

theorem stoppingPrefixDecision_bounds {Seed : Type*} [Fintype Seed]
    (seedLaw : PMF Seed) (rule : StoppingRule Seed A) (n : ℕ) (word : Fin n → A) :
    0 ≤ stoppingPrefixDecision seedLaw rule n word ∧
      stoppingPrefixDecision seedLaw rule n word ≤ 1 := by
  have hi (seed : Seed) :
      0 ≤ (if firstPositiveBy rule seed n word then (1 : ℝ) else 0) ∧
      (if firstPositiveBy rule seed n word then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  constructor
  · exact Finset.sum_nonneg (fun seed _ => mul_nonneg ENNReal.toReal_nonneg (hi seed).1)
  · have h := Finset.sum_le_sum (fun seed (_ : seed ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hi seed).2
        (ENNReal.toReal_nonneg : 0 ≤ (seedLaw seed).toReal))
    simpa only [stoppingPrefixDecision, mul_one, pmf_sum_real] using h

/-- The actual first-stop indicator is nested under literal word extension.
This is a pointwise interpreter property; no iid marginal or infinite-path
law is silently substituted for this finite statement. -/
theorem stoppingPrefixDecision_prefix_mono {Seed : Type*} [Fintype Seed]
    (seedLaw : PMF Seed) (rule : StoppingRule Seed A)
    {m n : ℕ} (hmn : m ≤ n) (word : Fin n → A) :
    stoppingPrefixDecision seedLaw rule m (fun i => word (Fin.castLE hmn i)) ≤
      stoppingPrefixDecision seedLaw rule n word := by
  unfold stoppingPrefixDecision
  apply Finset.sum_le_sum
  intro seed _
  by_cases h : firstPositiveBy rule seed m (fun i => word (Fin.castLE hmn i))
  · have hlong := firstPositiveBy_prefix_mono rule seed hmn word h
    simp only [if_pos h, if_pos hlong, le_refl]
  · simp only [if_neg h, mul_zero]
    split_ifs <;> positivity

/-- Actual finite-seed, finite-word stopping interpreter specialization.
Its observational supremum is constructed, not a supplied stopping law. -/
theorem no_uniform_finite_seed_stopping_at_wrong_closure
    {Seed : Type*} [Fintype Seed] (seedLaw : PMF Seed)
    (rule : StoppingRule Seed A) (p : PMF A) (laws : Set (PMF A))
    (beta alpha : ℝ) (hb : 0 ≤ beta) (halpha : 2 * alpha < 1)
    (hcorrect : ∀ z : PMF A, pmfTV p z ≤ beta →
      1 - alpha ≤ eventualAcceptance z (stoppingPrefixDecision seedLaw rule))
    (hsound : ∀ q ∈ expanded laws beta,
      eventualAcceptance q (stoppingPrefixDecision seedLaw rule) ≤ alpha)
    (hboundary : ∃ q ∈ tvClosure laws, pmfTV p q ≤ 2 * beta) : False := by
  exact no_uniform_prefix_stopping_at_wrong_closure p laws beta alpha hb halpha
    (stoppingPrefixDecision seedLaw rule) (stoppingPrefixDecision_bounds seedLaw rule)
    hcorrect hsound hboundary

#print axioms prefix_acceptance_bddAbove
#print axioms prefix_acceptance_le_eventual
#print axioms eventualAcceptance_bounds
#print axioms eventual_upper_bound_on_tvClosure
#print axioms no_uniform_prefix_stopping_at_wrong_closure
#print axioms firstPositiveBy_prefix_mono
#print axioms stoppingPrefixDecision_bounds
#print axioms stoppingPrefixDecision_prefix_mono
#print axioms no_uniform_finite_seed_stopping_at_wrong_closure

end UnifiedLean.G6.SequentialPrefixClosureObstruction
