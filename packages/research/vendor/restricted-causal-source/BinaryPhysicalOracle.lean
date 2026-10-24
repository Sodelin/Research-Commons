import BinaryOriginalSourceLabels
import BinarySelectionQuerySemantics

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual physical elementary-query adapter. Baseline CI is computed from
normalized selected finite product-law cell masses; invariance compares
the actual common-baseline and named replacement conditional ratios.
Faithfulness is retained in the admitted source type and its nonemptiness
for EVERY original finite DAG is proved from D1–D6 bodies. It is not
assumed via ExactResponse, and it is not inferred for arbitrary CPTs.

The response Boolean is a noncomputable exact-population specification.
No statistical estimator, sampling cost, numerical extraction or hard
intervention semantics is provided. Selection variables in a CI's
conditioning set are fixed at one under the selected law.
-/

namespace RestrictedCausal.PhysicalSource

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget FiniteTargetImage FiniteGraphDecision TranscriptDecoder GraphEquivalence
open ProbabilitySource ProbabilitySource.BinaryCPT PartialQueries

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]
variable (T : X → Prop) [DecidablePred T]

abbrev originalTarget (D : FiniteSource X) : {x : X // T x} → OriginalVertex D :=
  fun t => Observed t.val

abbrev OriginalCoordinate (D : FiniteSource X) := SharedCoordinate D.dag.arrow (originalTarget T D)

structure FaithfulParameters (D : FiniteSource X) where
  theta : OriginalCoordinate T D → ℚ
  positive : ∀ k, 0 < theta k ∧ theta k < 1
  baseline : SelectedBinaryFaithful D.dag.arrow
    (theta ∘ baselineCoordinate D.dag.arrow (originalTarget T D)) (originalSelection D)
  indicators : ∀ t : {x : X // T x}, SelectedBinaryFaithful (AddIndicator D.dag.arrow (Observed t.val))
    (theta ∘ singleIndicatorCoordinate D.dag.arrow (originalTarget T D) t)
    (liftedSelection (originalSelection D))

/-- Every original finite latent/selection source has a genuine common
positive binary realization in the admitted faithful class. The witness
is not a collection of separately chosen indicator distributions. -/
theorem faithful_parameters_nonempty (D : FiniteSource X) : Nonempty (FaithfulParameters T D) := by
  classical
  obtain ⟨theta, positive, baseline, indicators, _⟩ := exists_common_positive_faithful_source
    D.dag.arrow D.dag.acyclic (originalTarget T D) (originalSelection D) (original_selection_sinks D)
  exact ⟨⟨theta, positive, baseline, indicators⟩⟩

structure PhysicalSource where
  graph : FiniteSource X
  parameters : FaithfulParameters T graph

noncomputable def realize (D : FiniteSource X) : PhysicalSource T :=
  ⟨D, Classical.choice (faithful_parameters_nonempty T D)⟩

theorem realize_graph (D : FiniteSource X) : (realize T D).graph = D := rfl

noncomputable def baselineLaw (P : PhysicalSource T) : FiniteBinaryLaw (OriginalVertex P.graph) :=
  selectedBinaryLaw P.graph.dag.arrow P.graph.dag.acyclic
    (P.parameters.theta ∘ baselineCoordinate P.graph.dag.arrow (originalTarget T P.graph))
    (fun k => P.parameters.positive _) (originalSelection P.graph)

def BaselineIndependent (P : PhysicalSource T) (x y : X) (b : X → Bool) : Prop :=
  LawConditionalIndependent (baselineLaw T P) (Observed x) (Observed y) (originalCondition P.graph b)

def RegimeInvariant (P : PhysicalSource T) (t : {x : X // T x}) (x : X) (b : X → Bool) : Prop :=
  SelectedRegimeInvariant P.graph.dag.arrow (originalTarget T P.graph) t P.parameters.theta
    (originalSelection P.graph) (originalCondition P.graph b) (Observed x)

theorem baseline_ci_observed_only (P : PhysicalSource T) (x y : X) (b : X → Bool)
    (xOutside : ¬ BoolCondition b x) (yOutside : ¬ BoolCondition b y) :
    BaselineIndependent T P x y b ↔
      LawConditionalIndependent (baselineLaw T P) (Observed x) (Observed y)
        (originalCondition P.graph b \ originalSelection P.graph) :=
  selected_law_ci_remove_selection P.graph.dag.arrow P.graph.dag.acyclic _
    (fun k => P.parameters.positive _) (originalSelection P.graph) (originalCondition P.graph b)
    (original_selection_contained P.graph b) (Observed x) (Observed y)
    (observed_outside_original_condition P.graph b x xOutside)
    (observed_outside_original_condition P.graph b y yOutside)

theorem baseline_independent_exact (P : PhysicalSource T) (x y : X) (b : X → Bool)
    (different : x ≠ y) (xOutside : ¬ BoolCondition b x) (yOutside : ¬ BoolCondition b y) :
    BaselineIndependent T P x y b ↔
      ¬ ActiveConnection (arrowGraph P.graph.dag.arrow) (SelectedCondition (BoolCondition b))
        (Observed x) (Observed y) := by
  have distinctLabels : (Observed x : OriginalVertex P.graph) ≠ Observed y := by
    intro same
    exact different (Sum.inl.inj (Sum.inl.inj same))
  have leftOutside := observed_outside_original_condition P.graph b x xOutside
  have rightOutside := observed_outside_original_condition P.graph b y yOutside
  have selectedCI := selected_law_ci_iff P.graph.dag.arrow P.graph.dag.acyclic
    (P.parameters.theta ∘ baselineCoordinate P.graph.dag.arrow (originalTarget T P.graph))
    (fun k => P.parameters.positive _) (originalSelection P.graph) (originalCondition P.graph b)
    (original_selection_contained P.graph b) (Observed x) (Observed y) leftOutside rightOutside
  have faithful := P.parameters.baseline (Observed x) (Observed y) (originalCondition P.graph b)
    distinctLabels leftOutside rightOutside (original_selection_contained P.graph b)
  rw [original_condition_predicate P.graph b] at faithful
  exact selectedCI.trans faithful

theorem regime_invariant_exact (P : PhysicalSource T) (t : {x : X // T x}) (x : X) (b : X → Bool)
    (outside : ¬ BoolCondition b x) :
    RegimeInvariant T P t x b ↔
      ¬ ActiveConnection (arrowGraph (augmentSource P.graph.dag t.val).arrow)
        (SelectedCondition (InvarianceCondition (BoolCondition b))) (Observed none) (Observed (some x)) := by
  have numerical := faithful_selected_invariance_iff P.graph.dag.arrow (originalTarget T P.graph) t
    P.parameters.theta P.parameters.positive (originalSelection P.graph) (originalCondition P.graph b)
    (original_selection_contained P.graph b) (Observed x)
    (observed_outside_original_condition P.graph b x outside) (P.parameters.indicators t)
  exact numerical.trans (not_congr (original_indicator_connection P.graph t.val x b)).symm

def PhysicalPositiveAnswer (P : PhysicalSource T) : ElementaryAction X T → Prop
  | .ci x y b => if x ≠ y ∧ ¬ BoolCondition b x ∧ ¬ BoolCondition b y then
      BaselineIndependent T P x y b else False
  | .invariance t x b => if ¬ BoolCondition b x then RegimeInvariant T P t x b else False

noncomputable def physicalResponse (P : PhysicalSource T) (a : ElementaryAction X T) : Bool := by
  classical
  exact decide (PhysicalPositiveAnswer T P a)

/-- The graphical/physical elementary response contract is derived, with
illegal coordinates identically false on both sides. -/
theorem physical_positive_answer_exact (P : PhysicalSource T) (a : ElementaryAction X T) :
    PositiveAnswer P.graph a ↔ PhysicalPositiveAnswer T P a := by
  cases a with
  | ci x y b =>
      by_cases legal : x ≠ y ∧ ¬ BoolCondition b x ∧ ¬ BoolCondition b y
      · simpa only [PositiveAnswer, PhysicalPositiveAnswer, if_pos legal] using
          (baseline_independent_exact T P x y b legal.1 legal.2.1 legal.2.2).symm
      · simp only [PositiveAnswer, PhysicalPositiveAnswer, if_neg legal]
  | invariance t x b =>
      by_cases legal : ¬ BoolCondition b x
      · simpa only [PositiveAnswer, PhysicalPositiveAnswer, if_pos legal] using
          (regime_invariant_exact T P t x b legal).symm
      · simp only [PositiveAnswer, PhysicalPositiveAnswer, if_neg legal]

theorem physical_response_exact : ExactResponse (PhysicalSource.graph (T := T)) (physicalResponse T) := by
  classical
  intro P a
  simpa only [physicalResponse, decide_eq_true_eq] using physical_positive_answer_exact T P a

end RestrictedCausal.PhysicalSource
