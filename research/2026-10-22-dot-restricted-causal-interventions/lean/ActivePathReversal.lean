import DiscriminatingSectionExtraction

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Exact physical-trace reversal, including undirected MAG edges. No loop
reduction with a false no-tail-tail premise is used. Shortestness transfers
by reversing competing paths, so the dual discriminating-section orientation
can use the same actual path theorem rather than a symmetry assertion.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation DiscriminatingStatus
open SourceSelection (AncestorOf)

universe u

theorem vertex_path_realization {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (Z : V → Prop) (x y : V) {xs : List V} (h : Path G Z x y xs) :
    ∃ last states, Route (RealStep G Z) ⟨x, none⟩ states ⟨y, last⟩ ∧
      states.map Arrival.vertex = xs ∧ ((⟨x, none⟩ :: states).map Arrival.vertex).Nodup := by
  obtain ⟨route, nodup, good⟩ := h
  cases route with
  | nil => exact ⟨none, [], .nil _, rfl, nodup⟩
  | @cons x «next» y rest adjacent tail =>
      obtain ⟨«left», incoming, edge⟩ := adjacent
      obtain ⟨last, states, ready, «trace»⟩ := build_after_first G single Z tail x «left» incoming edge good
      refine ⟨last, ⟨«next», some incoming⟩ :: states,
        .cons ⟨«left», incoming, edge, rfl, trivial⟩ ready, ?_, ?_⟩
      · simpa only [List.map_cons, «trace»]
      · simpa only [List.map_cons, «trace»] using nodup

theorem reverse_active_route_trace {V : Type u} (G : MarkedGraph V)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (C A : V → Prop) {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C A) p xs q) :
    ∃ last ys, Route (Transition G C A) ⟨q.vertex, none⟩ ys ⟨p.vertex, last⟩ ∧
      (match p.incoming with | none => True | some previous => DepartureAllowed C A p.vertex last previous) ∧
      q.vertex :: ys.map Arrival.vertex = ((p :: xs).map Arrival.vertex).reverse := by
  induction h with
  | nil p =>
      refine ⟨none, [], .nil _, ?_, ?_⟩
      · cases p.incoming <;> trivial
      · simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append]
  | @cons p «next» q rest step tail ih =>
      obtain ⟨outgoing, incoming, edge, mark, active⟩ := step
      obtain ⟨last, ys, reversed, ready, «trace»⟩ := ih
      have backward : Transition G C A ⟨«next».vertex, last⟩ ⟨p.vertex, some outgoing⟩ := by
        refine ⟨incoming, outgoing, symmetric _ _ _ _ edge, rfl, ?_⟩
        simpa only [mark] using ready
      refine ⟨some outgoing, ys ++ [⟨p.vertex, some outgoing⟩],
        reversed.append (.cons backward (.nil _)), ?_, ?_⟩
      · cases hp : p.incoming with
        | none => trivial
        | some previous =>
            have atP : ActiveAt C A p.vertex previous outgoing := by simpa only [hp] using active
            exact (activeAt_swap C A p.vertex previous outgoing).mp atP
      · calc
          q.vertex :: (ys ++ [⟨p.vertex, some outgoing⟩]).map Arrival.vertex =
              (q.vertex :: ys.map Arrival.vertex) ++ [p.vertex] := by
                simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append]
          _ = ((«next» :: rest).map Arrival.vertex).reverse ++ [p.vertex] := by rw [«trace»]
          _ = ((p :: «next» :: rest).map Arrival.vertex).reverse := by
            simp only [List.map_cons, List.reverse_cons]

theorem reverse_path {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (Z : V → Prop) (x y : V) {xs : List V} (h : Path G Z x y xs) :
    ∃ ys, Path G Z y x ys ∧ y :: ys = (x :: xs).reverse ∧ ys.length = xs.length := by
  obtain ⟨last, states, route, originalTrace, nodup⟩ := vertex_path_realization G single Z x y h
  obtain ⟨reverseLast, reverseStates, reverseRoute, _, reverseTrace⟩ :=
    reverse_active_route_trace G symmetric Z (AncestorOf G Z) route
  have «trace» : y :: reverseStates.map Arrival.vertex = (x :: xs).reverse := by
    simpa only [List.map_cons, originalTrace] using reverseTrace
  have reverseNodup : ((⟨y, none⟩ :: reverseStates).map Arrival.vertex).Nodup := by
    rw [List.map_cons, «trace»]
    exact List.nodup_reverse.mpr h.2.1
  refine ⟨reverseStates.map Arrival.vertex,
    active_route_vertex_path G single Z y x reverseRoute reverseNodup, «trace», ?_⟩
  have length := congrArg List.length «trace»
  simp only [List.length_cons, List.length_reverse] at length
  omega

theorem reverse_shortest_path {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (Z : V → Prop) (x y : V) {xs : List V} (h : Shortest G Z x y xs) :
    ∃ ys, Shortest G Z y x ys ∧ y :: ys = (x :: xs).reverse ∧ ys.length = xs.length := by
  obtain ⟨ys, path, «trace», sameLength⟩ := reverse_path G single symmetric Z x y h.1
  refine ⟨ys, ⟨path, ?_⟩, «trace», sameLength⟩
  intro zs candidate
  obtain ⟨back, backPath, _, backLength⟩ := reverse_path G single symmetric Z y x candidate
  have bound := h.2 back backPath
  omega

end RestrictedCausal.VertexActivePaths
