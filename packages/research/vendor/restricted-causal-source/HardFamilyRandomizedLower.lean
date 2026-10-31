import HardFamilyUnboundedRuns
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

Arbitrary probability-space random seeds and genuinely unbounded adaptive
policies. Nontermination, including silent divergence with finitely many
queries, counts as failure. Expected query count is an extended nonnegative
Lebesgue integral; infinity is permitted. No finite-seed or bounded-horizon
replacement is made. Measurability is explicit probability regularity,
not an assumed causal-oracle or target-coupling lemma.
-/

namespace RestrictedCausal.HardFamily

open PartialQueries ProbabilitySource FiniteTargetImage TranscriptDecoder MeasureTheory
open GProgram.G7.ExactLawResourceGame
open scoped BigOperators ENNReal

universe uOmega

variable {k u : Nat} [LinearOrder (Labels k u)]

abbrev FamilyPolicy (k u : Nat) [LinearOrder (Labels k u)] :=
  Policy (ElementaryAction (Labels k u) Available) (Finset (TargetCode (Labels k u) Available))

noncomputable def everIndices (policy : FamilyPolicy k u) : Finset (Index u) := by
  classical
  exact Finset.univ.filter (EverTests policy)

theorem finite_tests_have_common_time (policy : FamilyPolicy k u) (s : Finset (Index u))
    (tested : ∀ q ∈ s, EverTests policy q) :
    ∃ n, ∀ q ∈ s, ∃ row ∈ (policyState promisedGame policy none n).history, TestsIndex q row.1 := by
  classical
  revert tested
  induction s using Finset.induction_on with
  | empty => intro tested; exact ⟨0, fun q member => (Finset.notMem_empty q member).elim⟩
  | @insert q s absent ih =>
      intro tested
      obtain ⟨m, row, member, test⟩ := tested q (Finset.mem_insert_self _ _)
      obtain ⟨n, common⟩ := ih (fun r present => tested r (Finset.mem_insert_of_mem present))
      refine ⟨max m n, ?_⟩
      intro r present
      rcases Finset.mem_insert.mp present with same | old
      · subst r
        exact ⟨row, policy_history_retains promisedGame policy none m (max m n) (le_max_left _ _) row member, test⟩
      · obtain ⟨oldRow, oldMember, oldTest⟩ := common r old
        exact ⟨oldRow, policy_history_retains promisedGame policy none n (max m n)
          (le_max_right _ _) oldRow oldMember, oldTest⟩

noncomputable def totalQueries (policy : FamilyPolicy k u) : ℝ≥0∞ :=
  ⨆ n : Nat, ((policyState promisedGame policy none n).history.length : ℝ≥0∞)

theorem everIndices_card_le_total (policy : FamilyPolicy k u) :
    ((everIndices policy).card : ℝ≥0∞) ≤ totalQueries policy := by
  classical
  obtain ⟨n, common⟩ := finite_tests_have_common_time policy (everIndices policy)
    (fun q member => (Finset.mem_filter.mp member).2)
  let history := (policyState promisedGame policy none n).history
  have subset : everIndices policy ⊆ testedIndices (history.map Prod.fst) := by
    intro q member
    obtain ⟨row, present, tested⟩ := common q member
    exact (mem_testedIndices q _).mpr
      ⟨row.1, List.mem_map.mpr ⟨row, present, rfl⟩, tested⟩
  have finiteBound : (everIndices policy).card ≤ history.length := by
    have «first» := Finset.card_le_card subset
    have second := testedIndices_card_le (history.map Prod.fst)
    rw [List.length_map] at second
    exact «first».trans second
  have castBound : ((everIndices policy).card : ℝ≥0∞) ≤ (history.length : ℝ≥0∞) := by
    exact_mod_cast finiteBound
  exact castBound.trans (le_iSup (fun m : Nat =>
    ((policyState promisedGame policy none m).history.length : ℝ≥0∞)) n)

def testEvent {Omega : Type uOmega} (policies : Omega → FamilyPolicy k u) (q : Index u) : Set Omega :=
  {seed | EverTests (policies seed) q}

def errorEvent {Omega : Type uOmega} (policies : Omega → FamilyPolicy k u)
    (source : Option (Index u)) : Set Omega :=
  {seed | PolicyError promisedGame (policies seed) source}

theorem untested_event_subset_errors {Omega : Type uOmega}
    (nonemptyTargets : 0 < k) (policies : Omega → FamilyPolicy k u) (q : Index u) :
    (testEvent policies q)ᶜ ⊆ errorEvent policies none ∪ errorEvent policies (some q) := by
  intro seed untested
  exact never_test_implies_error nonemptyTargets (policies seed) q untested

theorem test_probability_lower {Omega : Type uOmega} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (nonemptyTargets : 0 < k)
    (policies : Omega → FamilyPolicy k u) (epsilon : ℝ≥0∞)
    (errorBound : ∀ source, mu (errorEvent policies source) ≤ epsilon) (q : Index u)
    (measurableTest : MeasurableSet (testEvent policies q)) :
    1 - (epsilon + epsilon) ≤ mu (testEvent policies q) := by
  have complementBound : mu (testEvent policies q)ᶜ ≤ epsilon + epsilon :=
    (measure_mono (untested_event_subset_errors nonemptyTargets policies q)).trans
      ((measure_union_le _ _).trans (add_le_add (errorBound none) (errorBound (some q))))
  have oneBound : 1 ≤ mu (testEvent policies q) + (epsilon + epsilon) := by
    calc
      1 = mu (testEvent policies q) + mu (testEvent policies q)ᶜ :=
        (prob_add_prob_compl measurableTest).symm
      _ ≤ mu (testEvent policies q) + (epsilon + epsilon) := add_le_add_left complementBound _
  exact (tsub_le_iff_right).mpr oneBound

theorem test_indicator_sum_le_queries {Omega : Type uOmega}
    (policies : Omega → FamilyPolicy k u) (seed : Omega) :
    (∑ q : Index u, (testEvent policies q).indicator (fun _ => (1 : ℝ≥0∞)) seed) ≤
      totalQueries (policies seed) := by
  classical
  have count : (∑ q : Index u, (testEvent policies q).indicator (fun _ => (1 : ℝ≥0∞)) seed) =
      ((everIndices (policies seed)).card : ℝ≥0∞) := by
    change (∑ q : Index u, if EverTests (policies seed) q then (1 : ℝ≥0∞) else 0) =
      (((Finset.univ.filter (EverTests (policies seed))).card : Nat) : ℝ≥0∞)
    exact Finset.sum_boole _ _
  rw [count]
  exact everIndices_card_le_total (policies seed)

/-- The original randomized inequality with an arbitrary seed measure.
For real 0≤epsilon<1/2 the ENNReal expression is exactly
(1-2epsilon) choose(u,2) 2^(u-2). No integrability assumption is made:
infinite expected count satisfies the inequality automatically.

The final measurability premise makes the right side an actual extended
expectation. The proof of the inequality itself only needs the displayed
event regularity; it does not replace probabilistic CI by graphical bits. -/
theorem randomized_expected_query_lower {Omega : Type uOmega} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (nonemptyTargets : 0 < k)
    (policies : Omega → FamilyPolicy k u) (epsilon : ℝ≥0∞)
    (errorBound : ∀ source, mu (errorEvent policies source) ≤ epsilon)
    (_measurableErrors : ∀ source, MeasurableSet (errorEvent policies source))
    (measurableTests : ∀ q, MeasurableSet (testEvent policies q))
    (_measurableCount : Measurable (fun seed => totalQueries (policies seed))) :
    ((u.choose 2 * 2 ^ (u - 2) : Nat) : ℝ≥0∞) * (1 - (epsilon + epsilon)) ≤
      ∫⁻ seed, totalQueries (policies seed) ∂mu := by
  classical
  calc
    ((u.choose 2 * 2 ^ (u - 2) : Nat) : ℝ≥0∞) * (1 - (epsilon + epsilon)) =
        ∑ _q : Index u, (1 - (epsilon + epsilon)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, index_card]
    _ ≤ ∑ q : Index u, mu (testEvent policies q) :=
      Finset.sum_le_sum (fun q _ => test_probability_lower mu nonemptyTargets policies epsilon errorBound q (measurableTests q))
    _ = ∑ q : Index u, ∫⁻ seed, (testEvent policies q).indicator (fun _ => (1 : ℝ≥0∞)) seed ∂mu := by
      apply Finset.sum_congr rfl
      intro q _
      symm
      exact (lintegral_indicator_const (measurableTests q) 1).trans (one_mul _)
    _ = ∫⁻ seed, ∑ q : Index u, (testEvent policies q).indicator (fun _ => (1 : ℝ≥0∞)) seed ∂mu :=
      (lintegral_finsetSum Finset.univ (fun q _ => measurable_const.indicator (measurableTests q))).symm
    _ ≤ ∫⁻ seed, totalQueries (policies seed) ∂mu :=
      lintegral_mono (test_indicator_sum_le_queries policies)

/-- Final original physical-source statement. The error requirement is on
EVERY admitted common-mechanism source, while the lower expectation is on
one fixed baseline member. Its probability law, graph, label map and target
are the actual preceding constructions. No source is chosen per query. -/
theorem original_physical_randomized_lower {Omega : Type uOmega} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (nonemptyTargets : 0 < k)
    (policies : Omega → FamilyPolicy k u) (epsilon : ℝ≥0∞)
    (errorBound : ∀ P : PhysicalSource.PhysicalSource (@Available k u),
      mu {seed | PolicyError (PhysicalSource.physicalGame Available) (policies seed) P} ≤ epsilon)
    (measurableErrors : ∀ P : PhysicalSource.PhysicalSource (@Available k u),
      MeasurableSet {seed | PolicyError (PhysicalSource.physicalGame Available) (policies seed) P})
    (measurableTests : ∀ q, MeasurableSet (testEvent policies q))
    (measurableCount : Measurable (fun seed => totalQueries (policies seed))) :
    ((u.choose 2 * 2 ^ (u - 2) : Nat) : ℝ≥0∞) * (1 - (epsilon + epsilon)) ≤
      ∫⁻ seed, (⨆ n : Nat,
        ((policyState (PhysicalSource.physicalGame Available) (policies seed)
          (physicalSource (k := k) (u := u) none) n).history.length : ℝ≥0∞)) ∂mu := by
  have restricted : ∀ source, mu (errorEvent policies source) ≤ epsilon := by
    intro source
    have same : errorEvent policies source =
        {seed | PolicyError (PhysicalSource.physicalGame Available) (policies seed) (physicalSource source)} := by
      apply Set.ext
      intro seed
      exact (original_physical_policy_error (policies seed) source).symm
    rw [same]
    exact errorBound (physicalSource source)
  have measurableRestricted : ∀ source, MeasurableSet (errorEvent policies source) := by
    intro source
    have same : errorEvent policies source =
        {seed | PolicyError (PhysicalSource.physicalGame Available) (policies seed) (physicalSource source)} := by
      apply Set.ext
      intro seed
      exact (original_physical_policy_error (policies seed) source).symm
    rw [same]
    exact measurableErrors (physicalSource source)
  have «bound» := randomized_expected_query_lower mu nonemptyTargets policies epsilon restricted
    measurableRestricted measurableTests measurableCount
  simpa only [totalQueries, original_physical_policy_state] using «bound»

end RestrictedCausal.HardFamily
