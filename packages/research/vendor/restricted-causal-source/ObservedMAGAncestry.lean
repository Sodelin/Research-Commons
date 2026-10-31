import MAGMaximality

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The original-to-MAG ancestry direction is proved, without a representation
oracle, at every observed vertex that is not an ancestor of selection. In
particular this covers every vertex incident to a MAG arrowhead. This is a
classical representation component, not a new causal identifiability claim.
-/

namespace RestrictedCausal.HPLTarget

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open SourceSelection (AncestorOf)

universe u v w

theorem projected_observed_edge_inducing {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {mx my : Mark}
    (h : (extracted D).observed.edge x y mx my) : InducingPath D x y := by
  have hxy : x ≠ y := by
    intro eq
    subst y
    exact (extracted_observed_laws D).irreflexive x mx my h
  apply (inducing_iff_inseparable D x y).mpr
  refine ⟨hxy, ?_⟩
  intro Z _ _
  apply (original_projection_connection_iff D (SourceSelection.Condition Z) (.inl x) (.inl y)).mpr
  refine ⟨some my, [⟨.inl y, some my⟩], .cons ?_ (.nil _), ?_⟩
  · exact ⟨mx, my, h, rfl, trivial⟩
  · simpa using (show ([Sum.inl x, Sum.inl y] : List (Sum X S)).Nodup by simp [hxy])

theorem projected_observed_directed_reach {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} (h : Directed (extracted D).observed x y) :
    Reach (arrowGraph D.arrow) (Observed x) (Observed y) :=
  (retained_reach_exact D (.inl x) (.inl y)).mpr ⟨[.inl y], .cons h (.nil _)⟩

theorem projected_directed_edge_is_mag {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} (h : Directed (extracted D).observed x y)
    (hn : ¬ SelectionAncestor D x) : Directed (mag D) x y := by
  have inducing := projected_observed_edge_inducing D h
  have reach := projected_observed_directed_reach D h
  refine ⟨inducing, (endpoint_tail_iff D x y).mpr (Or.inl reach),
    (endpoint_head_iff D y x).mpr ?_⟩
  rintro (back | selected)
  · have equal := reach_antisymm_of_acyclic (arrowGraph D.arrow) (source_directed_acyclic D) reach back
    exact inducing.1 (Sum.inl.inj (Sum.inl.inj equal))
  · exact hn (selection_ancestor_predecessor D reach selected)

theorem observed_projected_route_is_mag {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {xs : List X}
    (h : Route (Directed (extracted D).observed) x xs y) :
    ¬ SelectionAncestor D x → Route (Directed (mag D)) x xs y := by
  induction h with
  | nil x => intro _; exact .nil x
  | cons step tail ih =>
      intro notSelected
      have edge := projected_directed_edge_is_mag D step notSelected
      exact .cons edge (ih (directed_target_not_selection_ancestor D edge))

theorem source_reach_is_mag_reach {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X}
    (h : Reach (arrowGraph D.arrow) (Observed x) (Observed y))
    (hn : ¬ SelectionAncestor D x) : Reach (mag D) x y := by
  have retained := (retained_reach_exact D (.inl x) (.inl y)).mp h
  rw [← extracted_graph_eq D] at retained
  obtain ⟨xs, route⟩ := (SourceSelection.observed_ancestry_exact (extracted D) x y).mp retained
  exact ⟨xs, observed_projected_route_is_mag D route hn⟩

theorem observed_ancestry_iff_not_selected {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} (hn : ¬ SelectionAncestor D x) :
    Reach (arrowGraph D.arrow) (Observed x) (Observed y) ↔ Reach (mag D) x y := by
  constructor
  · exact fun h => source_reach_is_mag_reach D h hn
  · rintro ⟨xs, route⟩
    exact mag_directed_route_lifts D route hn

/-- Exact collider-activation transfer. The selection-ancestry exclusion is
essential: it must not be removed or replaced by ordinary source ancestry. -/
theorem collider_ancestry_iff_not_selected {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x : X) (hn : ¬ SelectionAncestor D x) :
    AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) ↔
      AncestorOf (mag D) Z x := by
  constructor
  · rintro ⟨a, reach, conditioned⟩
    cases a with
    | inr latent => exact conditioned.elim
    | inl retained =>
        cases retained with
        | inr selected => exact (hn ⟨selected, reach⟩).elim
        | inl observed => exact ⟨observed, source_reach_is_mag_reach D reach hn, conditioned⟩
  · rintro ⟨y, ⟨xs, route⟩, hy⟩
    exact ⟨Observed y, mag_directed_route_lifts D route hn, hy⟩

end RestrictedCausal.HPLTarget
