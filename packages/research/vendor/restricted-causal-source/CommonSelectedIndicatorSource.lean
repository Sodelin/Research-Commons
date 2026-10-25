import CommonIndicatorRoots

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
The common canonical selected source, not independent indicator realizations.
Original arbitrary-latent projection and full MAG/TCM decoding remain explicit
downstream/upstream dependencies; no numerical-law equivalence is claimed.
-/

namespace RestrictedCausal.SourceSelection

open SelectedWalk CanonicalSelection GraphEquivalence
open LatentRoots (ActiveConnection)

universe u v

def selectedIndicatorVertexEquiv {X : Type u} {S : Type v} :
    Sum (Option X) S ≃ WithBot (Sum X S) where
  toFun a := match a with
    | .inl none => none
    | .inl (some x) => some (.inl x)
    | .inr s => some (.inr s)
  invFun b := match b with
    | none => .inl none
    | some (.inl x) => .inl (some x)
    | some (.inr s) => .inr s
  left_inv a := by
    rcases a with (a | s)
    · cases a <;> rfl
    · rfl
  right_inv b := by rcases b with _ | (x | s) <;> rfl

def selectedIndicatorGraphEquiv {X : Type u} {S : Type v}
    (H : SelectedGraph X S) (target : X) :
    MarkedEquiv (graph (augment H target))
      (LatentRoots.augmentGraph (graph H) (.inl target)) where
  toEquiv := selectedIndicatorVertexEquiv
  edge a b ma mb := by
    rcases a with (a | s) <;> rcases b with (b | t)
    · cases a <;> cases b <;>
        simp [graph, augment, augmentObserved, LatentRoots.augmentGraph,
          selectedIndicatorVertexEquiv]
    · cases a <;>
        simp [graph, augment, augmentObserved, LatentRoots.augmentGraph,
          selectedIndicatorVertexEquiv]
    · cases b <;>
        simp [graph, augment, augmentObserved, LatentRoots.augmentGraph,
          selectedIndicatorVertexEquiv]
    · exact Iff.rfl

def augmentedSelectedCondition {X : Type u} {S : Type v}
    (Z : Option X → Prop) : WithBot (Sum X S) → Prop
  | none => Z none
  | some (.inl x) => Z (some x)
  | some (.inr _) => True

def selectedIndicatorObserved {X : Type u} {S : Type v} : Option X → WithBot (Sum X S)
  | none => none
  | some x => some (.inl x)

theorem selectedIndicator_condition {X : Type u} {S : Type v}
    (Z : Option X → Prop) (a : Sum (Option X) S) :
    Condition Z a ↔ augmentedSelectedCondition Z (selectedIndicatorVertexEquiv a) := by
  rcases a with (a | s)
  · cases a <;> exact Iff.rfl
  · exact Iff.rfl

theorem selectedIndicator_observed {X : Type u} {S : Type v} (x : Option X) :
    selectedIndicatorVertexEquiv (.inl x : Sum (Option X) S) = selectedIndicatorObserved x := by
  cases x <;> rfl

theorem selected_augment_active_iff {X : Type u} {S : Type v}
    (H : SelectedGraph X S) (target : X) (Z : Option X → Prop) (x y : Option X) :
    ActivePath (augment H target) Z x y ↔
      ActiveConnection (LatentRoots.augmentGraph (graph H) (.inl target))
        (augmentedSelectedCondition Z) (selectedIndicatorObserved x) (selectedIndicatorObserved y) := by
  have h := (selectedIndicatorGraphEquiv H target).active_iff
    (selectedIndicator_condition Z) (.inl x) (.inl y)
  simpa only [selectedIndicatorGraphEquiv, selectedIndicator_observed] using h

/-- For every target and every conditioning set, add the named indicator to
ONE fixed actual baseline canonical DAG. Hidden-root labels, selectors and all
old source arrows stay fixed. Every untargeted observed variable remains in the
endpoint and conditioning-set quantifiers. This is a graphical source theorem,
not yet the original-DAG-to-TCM decoder or a statistical/sample claim. -/
theorem common_canonical_selected_indicator {X : Type u} {S : Type v}
    [LinearOrder X] (H : SelectedGraph X S) (laws : LatentRoots.MixedLaws H.observed)
    [LinearOrder (CanonicalSelection.Vertex (profile H))]
    (target : X) (Z : Option X → Prop) (x y : Option X) :
    ActivePath (augment H target) Z x y ↔
      ActiveConnection
        (LatentRoots.indicatorGraph (graph (canonical (profile H))) (.inl target))
        (LatentRoots.indicatorCondition (augmentedSelectedCondition Z))
        (LatentRoots.indicatorRetained (selectedIndicatorObserved x))
        (LatentRoots.indicatorRetained (selectedIndicatorObserved y)) := by
  have hprofile := (canonical_augmented_preservation H target).1 Z x y
  have hrelabel := selected_augment_active_iff (canonical (profile H)) target Z x y
  have hsource := LatentRoots.common_indicator_active_iff
    (graph (canonical (profile H))) (canonical_mixed_laws (profile H) laws) (.inl target)
    (augmentedSelectedCondition Z) (selectedIndicatorObserved x) (selectedIndicatorObserved y)
  exact hprofile.trans (hrelabel.trans hsource.symm)

theorem common_canonical_indicator_observed_ancestry {X : Type u} {S : Type v}
    [LinearOrder X] (H : SelectedGraph X S)
    [LinearOrder (CanonicalSelection.Vertex (profile H))]
    (target : X) (x y : Option X) :
    Reach (graph (augment H target)) (.inl x) (.inl y) ↔
      Reach (LatentRoots.indicatorGraph (graph (canonical (profile H))) (.inl target))
        (LatentRoots.indicatorRetained (selectedIndicatorObserved x))
        (LatentRoots.indicatorRetained (selectedIndicatorObserved y)) := by
  have hp := (canonical_augmented_preservation H target).2.1 x y
  have hr := (selectedIndicatorGraphEquiv (canonical (profile H)) target).reach_iff (.inl x) (.inl y)
  have hr' : Reach (graph (augment (canonical (profile H)) target)) (.inl x) (.inl y) ↔
      Reach (LatentRoots.augmentGraph (graph (canonical (profile H))) (.inl target))
        (selectedIndicatorObserved x) (selectedIndicatorObserved y) := by
    simpa only [selectedIndicatorGraphEquiv, selectedIndicator_observed] using hr
  have hs := LatentRoots.common_indicator_reach_iff (graph (canonical (profile H))) (.inl target)
    (selectedIndicatorObserved x) (selectedIndicatorObserved y)
  exact hp.trans (hr'.trans hs.symm)

theorem common_canonical_indicator_selection_ancestry {X : Type u} {S : Type v}
    [LinearOrder X] (H : SelectedGraph X S)
    [LinearOrder (CanonicalSelection.Vertex (profile H))]
    (target : X) (x : Option X) :
    (∃ s : S, Reach (graph (augment H target)) (.inl x) (.inr s)) ↔
      ∃ s : Selector (profile H),
        Reach (LatentRoots.indicatorGraph (graph (canonical (profile H))) (.inl target))
          (LatentRoots.indicatorRetained (selectedIndicatorObserved x)) (some (.inl (.inr s))) := by
  have hp := (canonical_augmented_preservation H target).2.2 x
  have one (s : Selector (profile H)) :
      Reach (graph (augment (canonical (profile H)) target)) (.inl x) (.inr s) ↔
        Reach (LatentRoots.indicatorGraph (graph (canonical (profile H))) (.inl target))
          (LatentRoots.indicatorRetained (selectedIndicatorObserved x)) (some (.inl (.inr s))) := by
    have hr := (selectedIndicatorGraphEquiv (canonical (profile H)) target).reach_iff (.inl x) (.inr s)
    have hr' : Reach (graph (augment (canonical (profile H)) target)) (.inl x) (.inr s) ↔
        Reach (LatentRoots.augmentGraph (graph (canonical (profile H))) (.inl target))
          (selectedIndicatorObserved x) (some (.inr s)) := by
      simpa only [selectedIndicatorGraphEquiv, selectedIndicator_observed,
        selectedIndicatorVertexEquiv] using hr
    have hs := LatentRoots.common_indicator_reach_iff (graph (canonical (profile H))) (.inl target)
      (selectedIndicatorObserved x) (some (.inr s))
    exact hr'.trans hs.symm
  refine hp.trans ?_
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, (one s).mp hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, (one s).mpr hs⟩

theorem canonical_actual_baseline_acyclic {X : Type u} [LinearOrder X]
    (Q : Profile X) [LinearOrder (CanonicalSelection.Vertex Q)]
    (hQ : LatentRoots.DirectedAcyclic Q.observed) :
    LatentRoots.DirectedAcyclic (LatentRoots.dagGraph (graph (canonical Q))) :=
  LatentRoots.dag_directed_acyclic (graph (canonical Q))
    (selected_directed_acyclic (canonical Q) hQ)

theorem canonical_actual_indicator_acyclic {X : Type u} [LinearOrder X]
    (Q : Profile X) [LinearOrder (CanonicalSelection.Vertex Q)]
    (hQ : LatentRoots.DirectedAcyclic Q.observed) (target : X) :
    LatentRoots.DirectedAcyclic
      (LatentRoots.indicatorGraph (graph (canonical Q)) (.inl target)) :=
  LatentRoots.indicator_dag_acyclic (graph (canonical Q))
    (selected_directed_acyclic (canonical Q) hQ) (.inl target)

theorem canonical_actual_indicator_selection_sink {X : Type u} [LinearOrder X]
    (Q : Profile X) [LinearOrder (CanonicalSelection.Vertex Q)]
    (target : X) (s : Selector Q)
    (b : Option (LatentRoots.Vertex (graph (canonical Q)))) :
    ¬ Directed (LatentRoots.indicatorGraph (graph (canonical Q)) (.inl target))
      (some (.inl (.inr s))) b := by
  intro h
  have ha := (LatentRoots.indicator_directed_exact (graph (canonical Q)) (.inl target)
    (some (.inl (.inr s))) b).mp h
  exact LatentRoots.indicator_preserves_sink (LatentRoots.Arrow (graph (canonical Q)))
    (.inl (.inl target)) (.inl (.inr s)) (canonical_dag_selection_sinks Q s) b ha

end RestrictedCausal.SourceSelection
