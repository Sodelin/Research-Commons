import CommonDiscriminatingParents

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Exact vertex-list semantics for the remaining MAG equivalence proof. On a
single-edge marked graph, local collider predicates recover the actual
chosen arrival incidences in both directions. This is a proved conversion
of the existing separation semantics, not a newly assumed path interface.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation DiscriminatingStatus
open SourceSelection (AncestorOf)
open WeakInducing (AllTriples)

universe u

def TripleActive {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (a b c : V) : Prop :=
  (Collider G a b c → AncestorOf G Z b) ∧ (¬ Collider G a b c → ¬ Z b)

def Path {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (x y : V) (xs : List V) : Prop :=
  Route (Adjacent G) x xs y ∧ (x :: xs).Nodup ∧ AllTriples (TripleActive G Z) (x :: xs)

theorem triple_active_iff_marks {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (Z : V → Prop) (a b c : V) (ma mb nb nc : Mark)
    (first : G.edge a b ma mb) (last : G.edge b c nb nc) :
    TripleActive G Z a b c ↔ ActiveAt Z (AncestorOf G Z) b mb nb := by
  classical
  have collider := collider_iff_chosen_marks G single a b c ma mb nb nc first last
  by_cases heads : mb = .head ∧ nb = .head
  · simp only [ActiveAt, if_pos heads]
    exact ⟨fun h => h.1 (collider.mpr heads), fun h =>
      ⟨fun _ => h, fun notCollider => (notCollider (collider.mpr heads)).elim⟩⟩
  · simp only [ActiveAt, if_neg heads]
    have noncollider : ¬ Collider G a b c := fun h => heads (collider.mp h)
    exact ⟨fun h => h.2 noncollider, fun h => ⟨fun hc => (noncollider hc).elim, fun _ => h⟩⟩

theorem active_route_triples_after_first {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (Z : V → Prop) {p q : Arrival V} {xs : List (Arrival V)}
    (route : Route (RealStep G Z) p xs q) :
    ∀ (a : V) (left incoming : Mark), G.edge a p.vertex left incoming → p.incoming = some incoming →
      AllTriples (TripleActive G Z) (a :: p.vertex :: xs.map Arrival.vertex) := by
  induction route with
  | nil p => intro _ _ _ _ _; trivial
  | @cons p next q rest step tail ih =>
      intro a left incoming first mark
      obtain ⟨outgoing, nextIncoming, edge, nextMark, active⟩ := step
      have atP : ActiveAt Z (AncestorOf G Z) p.vertex incoming outgoing := by
        simpa only [mark] using active
      exact ⟨(triple_active_iff_marks G single Z a p.vertex next.vertex
        left incoming outgoing nextIncoming first edge).mpr atP,
        ih p.vertex outgoing nextIncoming edge nextMark⟩

theorem active_connection_vertex_path {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (Z : V → Prop) (x y : V) (h : ActiveConnection G Z x y) : ∃ xs, Path G Z x y xs := by
  obtain ⟨last, xs, route, nodup⟩ := h
  refine ⟨xs.map Arrival.vertex, ?_, ?_, ?_⟩
  · exact route.map Arrival.vertex (by
      intro p q step
      obtain ⟨outgoing, incoming, edge, _, _⟩ := step
      exact ⟨outgoing, incoming, edge⟩)
  · exact nodup
  · cases route with
    | nil => trivial
    | @cons p next q rest step tail =>
        obtain ⟨left, incoming, edge, mark, _⟩ := step
        exact active_route_triples_after_first G single Z tail x left incoming edge mark

theorem build_after_first {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (Z : V → Prop) {b y : V} {xs : List V} (route : Route (Adjacent G) b xs y) :
    ∀ (a : V) (left incoming : Mark), G.edge a b left incoming →
      AllTriples (TripleActive G Z) (a :: b :: xs) →
      ∃ last states, Route (RealStep G Z) ⟨b, some incoming⟩ states ⟨y, last⟩ ∧
        states.map Arrival.vertex = xs := by
  induction route with
  | nil b => intro _ _ incoming _ _; exact ⟨some incoming, [], .nil _, rfl⟩
  | @cons b c y rest adjacent tail ih =>
      intro a left incoming first good
      obtain ⟨outgoing, nextIncoming, edge⟩ := adjacent
      have active := (triple_active_iff_marks G single Z a b c
        left incoming outgoing nextIncoming first edge).mp good.1
      obtain ⟨last, states, restRoute, trace⟩ := ih b outgoing nextIncoming edge good.2
      refine ⟨last, ⟨c, some nextIncoming⟩ :: states,
        .cons ⟨outgoing, nextIncoming, edge, rfl, active⟩ restRoute, ?_⟩
      simpa only [List.map_cons, trace]

theorem vertex_path_active_connection {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (Z : V → Prop) (x y : V) {xs : List V} (h : Path G Z x y xs) : ActiveConnection G Z x y := by
  obtain ⟨route, nodup, good⟩ := h
  cases route with
  | nil => exact ⟨none, [], .nil _, nodup⟩
  | @cons x b y rest adjacent tail =>
      obtain ⟨left, incoming, first⟩ := adjacent
      obtain ⟨last, states, restRoute, trace⟩ := build_after_first G single Z tail x left incoming first good
      refine ⟨last, ⟨b, some incoming⟩ :: states,
        .cons ⟨left, incoming, first, rfl, trivial⟩ restRoute, ?_⟩
      simpa only [List.map_cons, trace] using nodup

theorem active_connection_iff_vertex_path {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G) (Z : V → Prop) (x y : V) :
    ActiveConnection G Z x y ↔ ∃ xs, Path G Z x y xs :=
  ⟨active_connection_vertex_path G single Z x y,
    fun ⟨_, h⟩ => vertex_path_active_connection G single Z x y h⟩

end RestrictedCausal.VertexActivePaths
