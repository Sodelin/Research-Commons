import DiscriminatingStatusTransport

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Locate every actual discriminating-prefix collider in the proved dependency
interval. The complete oriented trace and span are used, including reversed
positions. Thus the whole-path induction can supply the local transport
premise without assuming a correspondence between unrelated witnesses.
-/

namespace RestrictedCausal.IndexedDiscriminatingSections

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection HPLTarget
open InducingSeparation DiscriminatingStatus VertexActivePaths WeakInducing
open DiscriminatingIntervalGeometry

universe u v w

theorem collider_reverse_of_symmetric {X : Type u} (G : MarkedGraph X)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    {a b c : X} (collider : Collider G a b c) : Collider G c b a := by
  obtain ⟨«left», «right», «first», last⟩ := collider
  exact ⟨«right», «left», symmetric b c .head «right» last, symmetric a b «left» .head «first»⟩

theorem collider_swap_iff {X : Type u} (G : MarkedGraph X)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma) (a b c : X) :
    Collider G a b c ↔ Collider G c b a :=
  ⟨collider_reverse_of_symmetric G symmetric, collider_reverse_of_symmetric G symmetric⟩

theorem all_triples_of_trace {X : Type u} (vertex : Nat → X) (P : X → X → X → Prop)
    (xs : List X) :
    ∀ offset, Trace vertex offset xs →
      (∀ i, offset < i → i + 1 < offset + xs.length →
        P (vertex (i - 1)) (vertex i) (vertex (i + 1))) → AllTriples P xs := by
  induction xs with
  | nil => intro _ _ _; trivial
  | cons a rest ih =>
      intro offset «trace» atPosition
      cases rest with
      | nil => trivial
      | cons b rest =>
          cases rest with
          | nil => trivial
          | cons c tail =>
              constructor
              · have localStatus := atPosition (offset + 1) (by omega) (by
                  simp only [List.length_cons]
                  omega)
                have previous : offset + 1 - 1 = offset := by omega
                simpa only [previous, «trace».1, «trace».2.1, «trace».2.2.1] using localStatus
              · apply ih (offset + 1) «trace».2
                intro i lower upper
                exact atPosition i (by omega) (by simp only [List.length_cons] at upper ⊢; omega)

theorem witness_prefix_trace {X : Type u} {G : MarkedGraph X} {a b c : X}
    (w : DiscriminatingWitness G a b c) (vertex : Nat → X) (offset : Nat)
    («trace» : Trace vertex offset w.vertices) :
    Trace vertex offset (((⟨w.start, none⟩ :: w.parents).map Arrival.vertex) ++ [b]) := by
  have «split» : w.vertices =
      ((((⟨w.start, none⟩ :: w.parents).map Arrival.vertex) ++ [b]) ++ [c]) := by
    simp only [DiscriminatingWitness.vertices, List.map_cons, List.map_append, List.map_nil,
      List.cons_append, List.append_assoc, List.singleton_append, w.terminal_vertex]
  rw [«split»] at «trace»
  exact ((trace_append vertex _ [c] offset).mp «trace»).1

theorem indexed_prefix_colliders {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (H : MarkedGraph X)
    (symmetricH : ∀ a b ma mb, H.edge a b ma mb → H.edge b a mb ma)
    (vertex : Nat → X) {center : Nat} (w : IndexedWitness D vertex center)
    (earlier : ∀ i, Interior w.start center i →
      Collider H (vertex (i - 1)) (vertex i) (vertex (i + 1))) :
    AllTriples (Collider H)
      ((((⟨w.witness.start, none⟩ :: w.witness.parents).map Arrival.vertex)) ++ [vertex center]) := by
  rcases w.position_trace with forward | backward
  · have span := w.span.1 forward.1
    have «trace» := witness_prefix_trace w.witness vertex w.start forward.2
    apply all_triples_of_trace vertex (Collider H) _ w.start «trace»
    intro i lower upper
    have inside : Interior w.start center i := Or.inl ⟨lower, by
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at upper
      omega⟩
    exact earlier i inside
  · have span := w.span.2 backward.1
    have «trace» := witness_prefix_trace w.witness (fun i => vertex (w.start - i)) 0 backward.2
    apply all_triples_of_trace (fun i => vertex (w.start - i)) (Collider H) _ 0 «trace»
    intro i lower upper
    have localBound : i ≤ w.witness.parents.length := by
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at upper
      omega
    have inside : Interior w.start center (w.start - i) := Or.inr ⟨by omega, by omega⟩
    have localStatus := collider_reverse_of_symmetric H symmetricH (earlier (w.start - i) inside)
    have previous : w.start - (i - 1) = w.start - i + 1 := by omega
    have following : w.start - (i + 1) = w.start - i - 1 := by omega
    simpa only [previous, following] using localStatus

theorem indexed_status_to_standard {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (H : MarkedGraph X)
    (symmetricH : ∀ a b ma mb, H.edge a b ma mb → H.edge b a mb ma)
    (vertex : Nat → X) {center : Nat} (w : IndexedWitness D vertex center)
    («local» : Collider (mag D) (vertex w.before) (vertex center) (vertex w.finish) ↔
      Collider H (vertex w.before) (vertex center) (vertex w.finish)) :
    Collider (mag D) (vertex (center - 1)) (vertex center) (vertex (center + 1)) ↔
      Collider H (vertex (center - 1)) (vertex center) (vertex (center + 1)) := by
  rcases w.orientation with forward | backward
  · have previous : w.before = center - 1 := by omega
    simpa only [previous, forward.2.2] using «local»
  · have following : w.finish = center - 1 := by omega
    have reversed : Collider (mag D) (vertex (center + 1)) (vertex center) (vertex (center - 1)) ↔
        Collider H (vertex (center + 1)) (vertex center) (vertex (center - 1)) := by
      simpa only [backward.2.1, following] using «local»
    exact (collider_swap_iff (mag D) (mag_symmetric D) _ _ _).trans
      (reversed.trans (collider_swap_iff H symmetricH _ _ _))

end RestrictedCausal.IndexedDiscriminatingSections
