import WeakInducingEdges

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Construct the initial observed-simple weak route from an arbitrary original
selected active path. Hidden colliders and overlapping latent expansions are
already handled by the original projection theorem. Selection-only blocks
are contracted using the actual extraction and its proved marked bridges.
-/

namespace RestrictedCausal.WeakInducing

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open SourceSelection (AncestorOf)

universe u v w

def Connection {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) : Prop :=
  ∃ last xs, Route (Transition (graph D) Z (Activated D Z)) ⟨x, none⟩ xs ⟨y, last⟩ ∧
    ((⟨x, none⟩ :: xs).map Arrival.vertex).Nodup

def observedState {X : Type u} {S : Type v} (fallback : X) (p : Arrival (Sum X S)) : Arrival X :=
  ⟨match p.vertex with | .inl x => x | .inr _ => fallback, p.incoming⟩

theorem source_projected_observed_activity {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x : X) (incoming outgoing : Mark) :
    ActiveAt (SourceSelection.Condition Z)
      (AncestorOf (SourceSelection.graph (extracted D)) (SourceSelection.Condition Z))
      (.inl x) incoming outgoing ↔ ActiveAt Z (Activated D Z) x incoming outgoing := by
  rw [extracted_graph_eq D]
  exact (original_retained_activity D (SourceSelection.Condition Z) (.inl x) incoming outgoing).symm

theorem compressed_step_is_weak {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (fallback : X)
    {p q : Arrival (Sum X S)}
    (h : SourceSelection.CompressedTransition (extracted D) (SourceSelection.Condition Z)
      (AncestorOf (SourceSelection.graph (extracted D)) (SourceSelection.Condition Z)) p q) :
    Transition (graph D) Z (Activated D Z) (observedState fallback p) (observedState fallback q) := by
  obtain ⟨x, y, outgoing, incoming, hp, hq, mark, active, edge⟩ := h
  rcases p with ⟨pv, pm⟩
  rcases q with ⟨qv, qm⟩
  change pv = .inl x at hp
  change qv = .inl y at hq
  subst pv
  subst qv
  refine ⟨outgoing, incoming, ?_, mark, ?_⟩
  · rcases edge with direct | bridge
    · exact observed_projected_edge_weak D direct
    · exact selection_bridge_weak D bridge
  · cases pm with
    | none => trivial
    | some previous => exact (source_projected_observed_activity D Z x previous outgoing).mp active

theorem observed_map_nodup {X : Type u} {S : Type v}
    (fallback : X) {xs : List (Arrival (Sum X S))}
    (allObserved : ∀ p ∈ xs, SourceSelection.IsObserved p)
    (nodup : (xs.map Arrival.vertex).Nodup) :
    ((xs.map (observedState fallback)).map Arrival.vertex).Nodup := by
  have pairs : xs.Pairwise (fun p q => p.vertex ≠ q.vertex) := by
    simpa only [List.Nodup, List.pairwise_map] using nodup
  rw [List.map_map, List.Nodup, List.pairwise_map]
  apply pairs.imp_of_mem
  intro p q hp hq distinct same
  obtain ⟨x, px⟩ := allObserved p hp
  obtain ⟨y, qy⟩ := allObserved q hq
  have equal : x = y := by simpa only [Function.comp_apply, observedState, px, qy] using same
  exact distinct (px.trans ((congrArg Sum.inl equal).trans qy.symm))

theorem original_connection_is_weak {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X)
    (h : ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y)) :
    Connection D Z x y := by
  have projected := (original_projection_connection_iff D (SourceSelection.Condition Z) (.inl x) (.inl y)).mp h
  rw [← extracted_graph_eq D] at projected
  obtain ⟨last, xs, path, nodup⟩ := projected
  have pairs : (⟨.inl x, none⟩ :: xs).Pairwise
      (fun p q : Arrival (Sum X S) => p.vertex ≠ q.vertex) := by
    simpa only [List.Nodup, List.pairwise_map] using nodup
  have noObservedRepeat : NoObservedRepeat SourceSelection.isSelected (⟨.inl x, none⟩ :: xs) :=
    pairs.imp (fun {_ _} neq eq => (neq eq).elim)
  obtain ⟨ys, compressed, sublist⟩ := SourceSelection.contract_active_route (extracted D) path noObservedRepeat
  have allObserved := SourceSelection.compressed_route_observed (extracted D) compressed ⟨x, rfl⟩
  have shortNodup := List.Nodup.sublist (List.Sublist.map Arrival.vertex (List.Sublist.cons_cons _ sublist)) nodup
  have mapped := compressed.map (observedState x)
    (fun _ _ step => compressed_step_is_weak D Z x step)
  refine ⟨last, ys.map (observedState x), mapped, ?_⟩
  simpa only [List.map_cons] using observed_map_nodup x allObserved shortNodup

end RestrictedCausal.WeakInducing
