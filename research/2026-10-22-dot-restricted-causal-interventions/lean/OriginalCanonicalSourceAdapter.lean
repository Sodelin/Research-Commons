import OriginalIndicatorProjection

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Compose the ACTUAL arbitrary-latent original DAG with one bounded canonical
source, for the baseline and every named single-root augmentation.
HPL MAG/TCM interpretation, probability witnesses and the final decoder are
still separate full-theorem dependencies, not replaced by these graph data.
-/

namespace RestrictedCausal.OriginalProjection

open SelectedWalk CanonicalSelection LatentRoots

universe u v w

abbrev sourceProfile {X : Type u} {S : Type v} {L : Type w} (D : SourceDAG X S L) :=
  SourceSelection.profile (extracted D)

abbrev canonicalRetainedGraph {X : Type u} {S : Type v} {L : Type w} [LinearOrder X]
    (D : SourceDAG X S L) := SourceSelection.graph (SourceSelection.canonical (sourceProfile D))

theorem original_selected_baseline_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) :
    ActiveConnection (arrowGraph D.arrow) (retainedCondition (SourceSelection.Condition Z))
      (.inl (.inl x)) (.inl (.inl y)) ↔ SourceSelection.ActivePath (extracted D) Z x y := by
  have h := original_projection_connection_iff D (SourceSelection.Condition Z) (.inl x) (.inl y)
  rw [← extracted_graph_eq D] at h
  exact h

theorem original_selected_indicator_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) (Z : Option X → Prop) (x y : Option X) :
    ActiveConnection (arrowGraph (augmentSource D target).arrow)
      (retainedCondition (SourceSelection.Condition Z)) (.inl (.inl x)) (.inl (.inl y)) ↔
      SourceSelection.ActivePath (SourceSelection.augment (extracted D) target) Z x y := by
  have h := original_projection_connection_iff (augmentSource D target)
    (SourceSelection.Condition Z) (.inl x) (.inl y)
  rw [projection_augmentation_exact D target] at h
  exact h

theorem original_canonical_baseline_connection {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))]
    (Z : X → Prop) (x y : X) :
    ActiveConnection (arrowGraph D.arrow) (retainedCondition (SourceSelection.Condition Z))
      (.inl (.inl x)) (.inl (.inl y)) ↔
      ActiveConnection (dagGraph (canonicalRetainedGraph D))
        (liftCondition (SourceSelection.Condition Z)) (.inl (.inl x)) (.inl (.inl y)) :=
  (original_selected_baseline_iff D Z x y).trans
    (SourceSelection.canonical_dag_selected_preservation (extracted D) (extracted_observed_laws D) Z x y)

/-- Full original-source and all-observed-variable quantifiers. The canonical
baseline DAG is fixed before target is supplied; no indicator-specific source
or latent/selection registry is chosen by this theorem. -/
theorem original_canonical_indicator_connection {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))]
    (target : X) (Z : Option X → Prop) (x y : Option X) :
    ActiveConnection (arrowGraph (augmentSource D target).arrow)
      (retainedCondition (SourceSelection.Condition Z)) (.inl (.inl x)) (.inl (.inl y)) ↔
      ActiveConnection (indicatorGraph (canonicalRetainedGraph D) (.inl target))
        (indicatorCondition (SourceSelection.augmentedSelectedCondition Z))
        (indicatorRetained (SourceSelection.selectedIndicatorObserved x))
        (indicatorRetained (SourceSelection.selectedIndicatorObserved y)) :=
  (original_selected_indicator_iff D target Z x y).trans
    (SourceSelection.common_canonical_selected_indicator (extracted D)
      (extracted_observed_laws D) target Z x y)

theorem original_canonical_baseline_observed_ancestry {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] (x y : X) :
    Reach (arrowGraph D.arrow) (.inl (.inl x)) (.inl (.inl y)) ↔
      Reach (dagGraph (canonicalRetainedGraph D)) (.inl (.inl x)) (.inl (.inl y)) := by
  have h := retained_reach_exact D (.inl x) (.inl y)
  rw [← extracted_graph_eq D] at h
  exact h.trans (((SourceSelection.canonical_same_profile (extracted D)).observedReach x y).trans
    (LatentRoots.retained_ancestry_exact (canonicalRetainedGraph D) (.inl x) (.inl y)).symm)

theorem original_canonical_indicator_observed_ancestry {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] (target : X) (x y : Option X) :
    Reach (arrowGraph (augmentSource D target).arrow) (.inl (.inl x)) (.inl (.inl y)) ↔
      Reach (indicatorGraph (canonicalRetainedGraph D) (.inl target))
        (indicatorRetained (SourceSelection.selectedIndicatorObserved x))
        (indicatorRetained (SourceSelection.selectedIndicatorObserved y)) := by
  have h := retained_reach_exact (augmentSource D target) (.inl x) (.inl y)
  rw [projection_augmentation_exact D target] at h
  exact h.trans (SourceSelection.common_canonical_indicator_observed_ancestry (extracted D) target x y)

theorem original_canonical_baseline_selection_ancestry {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] (x : X) :
    (∃ s : S, Reach (arrowGraph D.arrow) (.inl (.inl x)) (.inl (.inr s))) ↔
      ∃ s : Selector (sourceProfile D),
        Reach (dagGraph (canonicalRetainedGraph D)) (.inl (.inl x)) (.inl (.inr s)) := by
  have first : (∃ s : S, Reach (arrowGraph D.arrow) (.inl (.inl x)) (.inl (.inr s))) ↔
      ∃ s : S, Reach (SourceSelection.graph (extracted D)) (.inl x) (.inr s) := by
    have one (s : S) := retained_reach_exact D (.inl x) (.inr s)
    simp only [← extracted_graph_eq D] at one
    exact ⟨fun ⟨s, hs⟩ => ⟨s, (one s).mp hs⟩, fun ⟨s, hs⟩ => ⟨s, (one s).mpr hs⟩⟩
  have middle := (SourceSelection.canonical_same_profile (extracted D)).selectionReach x
  have last : (∃ s : Selector (sourceProfile D),
      Reach (canonicalRetainedGraph D) (.inl x) (.inr s)) ↔
      ∃ s : Selector (sourceProfile D),
        Reach (dagGraph (canonicalRetainedGraph D)) (.inl (.inl x)) (.inl (.inr s)) := by
    have one (s : Selector (sourceProfile D)) :=
      (LatentRoots.retained_ancestry_exact (canonicalRetainedGraph D) (.inl x) (.inr s)).symm
    exact ⟨fun ⟨s, hs⟩ => ⟨s, (one s).mp hs⟩, fun ⟨s, hs⟩ => ⟨s, (one s).mpr hs⟩⟩
  exact first.trans (middle.trans last)

theorem original_canonical_indicator_selection_ancestry {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] (target : X) (x : Option X) :
    (∃ s : S, Reach (arrowGraph (augmentSource D target).arrow) (.inl (.inl x)) (.inl (.inr s))) ↔
      ∃ s : Selector (sourceProfile D),
        Reach (indicatorGraph (canonicalRetainedGraph D) (.inl target))
          (indicatorRetained (SourceSelection.selectedIndicatorObserved x)) (some (.inl (.inr s))) := by
  have first : (∃ s : S, Reach (arrowGraph (augmentSource D target).arrow) (.inl (.inl x)) (.inl (.inr s))) ↔
      ∃ s : S, Reach (SourceSelection.graph (SourceSelection.augment (extracted D) target))
        (.inl x) (.inr s) := by
    have one (s : S) := retained_reach_exact (augmentSource D target) (.inl x) (.inr s)
    simp only [projection_augmentation_exact D target] at one
    exact ⟨fun ⟨s, hs⟩ => ⟨s, (one s).mp hs⟩, fun ⟨s, hs⟩ => ⟨s, (one s).mpr hs⟩⟩
  exact first.trans (SourceSelection.common_canonical_indicator_selection_ancestry (extracted D) target x)

/-- The exact finite bounds apply only to the constructed common source;
there is no hidden bound on the original S or L carriers. -/
theorem canonical_source_size_bounds {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] [Fintype X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] :
    Fintype.card (Selector (sourceProfile D)) ≤ Fintype.card X + 4 * (Fintype.card X).choose 2 ∧
      Fintype.card (Root (canonicalRetainedGraph D)) ≤ 9 * (Fintype.card X).choose 2 :=
  ⟨selector_card_bound (sourceProfile D), canonical_hidden_root_bound (sourceProfile D)⟩

theorem canonical_source_acyclic {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] :
    DirectedAcyclic (dagGraph (canonicalRetainedGraph D)) ∧
      ∀ target : X, DirectedAcyclic (indicatorGraph (canonicalRetainedGraph D) (.inl target)) :=
  ⟨SourceSelection.canonical_actual_baseline_acyclic (sourceProfile D) (extracted_observed_acyclic D),
    SourceSelection.canonical_actual_indicator_acyclic (sourceProfile D) (extracted_observed_acyclic D)⟩

end RestrictedCausal.OriginalProjection
