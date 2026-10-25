import DiscriminatingIntervalGeometry

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual list/position extraction for the collider-order dependency proof.
`Trace` explicitly equates each finite-list entry with its indexed vertex;
it is not an oracle for adjacency, collider order, or a graph adapter.
-/

namespace RestrictedCausal.IndexedDiscriminatingSections

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection HPLTarget
open InducingSeparation DiscriminatingStatus VertexActivePaths
open DiscriminatingIntervalGeometry

universe u v w

theorem trace_append {X : Type u} (vertex : Nat → X) (front back : List X) (offset : Nat) :
    Trace vertex offset (front ++ back) ↔
      Trace vertex offset front ∧ Trace vertex (offset + front.length) back := by
  induction front generalizing offset with
  | nil => simp only [List.nil_append, List.length_nil, Nat.add_zero, Trace, true_and]
  | cons x xs ih =>
      simp only [List.cons_append, Trace, List.length_cons, ih]
      have arithmetic : offset + 1 + xs.length = offset + (xs.length + 1) := by omega
      rw [arithmetic]
      exact and_assoc.symm

theorem trace_route_terminal {X : Type u} {R : X → X → Prop} (vertex : Nat → X)
    {p q : X} {xs : List X} (route : Route R p xs q) (offset : Nat)
    («trace» : Trace vertex offset (p :: xs)) : vertex (offset + xs.length) = q := by
  induction route generalizing offset with
  | nil p => simpa only [List.length_nil, Nat.add_zero] using «trace».1
  | @cons p «next» q rest step tail ih =>
      have endpoint := ih (offset + 1) «trace».2
      have arithmetic : offset + («next» :: rest).length = offset + 1 + rest.length := by
        simp only [List.length_cons]
        omega
      simpa only [arithmetic] using endpoint

theorem trace_arrival_terminal {X : Type u} {R : Arrival X → Arrival X → Prop}
    (vertex : Nat → X) {p q : Arrival X} {xs : List (Arrival X)}
    (route : Route R p xs q) (offset : Nat)
    («trace» : Trace vertex offset ((p :: xs).map Arrival.vertex)) :
    vertex (offset + xs.length) = q.vertex := by
  induction route generalizing offset with
  | nil p => simpa only [List.length_nil, Nat.add_zero] using «trace».1
  | @cons p «next» q rest step tail ih =>
      have endpoint := ih (offset + 1) «trace».2
      have arithmetic : offset + («next» :: rest).length = offset + 1 + rest.length := by
        simp only [List.length_cons]
        omega
      simpa only [arithmetic] using endpoint

/-- Every strict interior position of an actual collider-parent route has
both its neighboring head incidences and its actual arrow to the endpoint.
The proof uses the two consecutive transitions at that position, not an
asserted path/collider summary. -/
theorem indexed_parent_route {X : Type u} (G : MarkedGraph X) (y : X)
    (vertex : Nat → X) {p q : Arrival X} {xs : List (Arrival X)}
    (route : Route (ColliderParentStep G y) p xs q) :
    ∀ offset, Trace vertex offset ((p :: xs).map Arrival.vertex) →
      ∀ i, offset < i → i < offset + xs.length →
        Directed G (vertex i) y ∧
          Collider G (vertex (i - 1)) (vertex i) (vertex (i + 1)) := by
  induction route with
  | nil p => intro offset «trace» i lower upper; simp only [List.length_nil] at upper; omega
  | @cons p «next» q rest step tail ih =>
      intro offset «trace» i lower upper
      by_cases «first» : i = offset + 1
      · cases tail with
        | nil «next» => simp only [List.length_cons, List.length_nil] at upper; omega
        | @cons «next» after q remaining nextStep remainingRoute =>
            obtain ⟨«left», incoming, firstEdge, firstMark, _⟩ := step
            obtain ⟨outgoing, «right», secondEdge, secondMark, parent⟩ := nextStep
            have details : incoming = .head ∧ outgoing = .head ∧ Directed G «next».vertex y := by
              simpa only [firstMark] using parent
            have previousIndex : i - 1 = offset := by omega
            have nextIndex : i + 1 = offset + 1 + 1 := by omega
            have atPrevious : vertex (i - 1) = p.vertex := by simpa only [previousIndex] using «trace».1
            have atCurrent : vertex i = «next».vertex := by simpa only [«first»] using «trace».2.1
            have atNext : vertex (i + 1) = after.vertex := by
              simpa only [nextIndex] using «trace».2.2.1
            refine ⟨?_, «left», «right», ?_, ?_⟩
            · simpa only [atCurrent] using details.2.2
            · simpa only [atPrevious, atCurrent, details.1] using firstEdge
            · simpa only [atCurrent, atNext, details.2.1] using secondEdge
      · have nextLower : offset + 1 < i := by omega
        have nextUpper : i < offset + 1 + rest.length := by
          simp only [List.length_cons] at upper
          omega
        exact ih (offset + 1) «trace».2 i nextLower nextUpper

/-- Index a forward literal discriminating section at its actual offset.
All four endpoint/neighbor labels, every parent, and every interior collider
are extracted from the witness's actual routes and finite vertex list. -/
theorem index_forward_witness {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) {a b c : X}
    (w : DiscriminatingWitness (mag D) a b c) (offset : Nat)
    («trace» : Trace vertex offset w.vertices) :
    ∃ indexed : IndexedWitness D vertex (offset + w.parents.length + 1),
      indexed.start = offset ∧ indexed.before = offset + w.parents.length ∧
      indexed.finish = offset + w.parents.length + 2 ∧
      vertex (offset + w.parents.length + 1) = b := by
  have divided : Trace vertex offset
      ((⟨w.start, none⟩ :: (w.parents ++ [w.terminal])).map Arrival.vertex) ∧
      Trace vertex (offset + (((⟨w.start, none⟩ :: (w.parents ++ [w.terminal])).map Arrival.vertex).length)) [c] :=
    (trace_append vertex _ [c] offset).mp «trace»
  have prefixTrace : Trace vertex offset ((⟨w.start, none⟩ :: w.parents).map Arrival.vertex) := by
    have «split» : Trace vertex offset
        (((⟨w.start, none⟩ :: w.parents).map Arrival.vertex) ++ [w.terminal.vertex]) := by
      simpa only [List.map_cons, List.map_append, List.map_nil, List.cons_append] using divided.1
    exact ((trace_append vertex _ [w.terminal.vertex] offset).mp «split»).1
  have beforeTrace : vertex (offset + w.parents.length) = a :=
    (trace_arrival_terminal vertex w.parent_prefix offset prefixTrace).trans w.before_vertex
  have terminalTrace : vertex (offset + w.parents.length + 1) = b := by
    have result := (trace_arrival_terminal vertex w.prefix offset divided.1).trans w.terminal_vertex
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero, Nat.add_assoc] using result
  have finishTrace : vertex (offset + w.parents.length + 2) = c := by
    have result := divided.2.1
    simpa only [List.length_map, List.length_cons, List.length_append, List.length_nil,
      Nat.add_zero, Nat.add_assoc] using result
  have startTrace : vertex offset = w.start := divided.1.1
  have positive : 0 < w.parents.length := by
    cases parentsEq : w.parents with
    | nil => exact (w.nonempty parentsEq).elim
    | cons p ps => simp only [List.length_cons]; omega
  let actual : DiscriminatingWitness (mag D) (vertex (offset + w.parents.length))
      (vertex (offset + w.parents.length + 1)) (vertex (offset + w.parents.length + 2)) := {
    start := w.start, before := w.before, terminal := w.terminal, parents := w.parents,
    before_vertex := w.before_vertex.trans beforeTrace.symm,
    terminal_vertex := w.terminal_vertex.trans terminalTrace.symm,
    parent_prefix := by simpa only [finishTrace] using w.parent_prefix,
    last_parent_step := by simpa only [finishTrace] using w.last_parent_step,
    terminal_adjacent := by simpa only [terminalTrace, finishTrace] using w.terminal_adjacent,
    nonempty := w.nonempty,
    simple := by simpa only [finishTrace] using w.simple,
    nonadjacent := by simpa only [finishTrace] using w.nonadjacent }
  refine ⟨{
    start := offset
    before := offset + w.parents.length
    finish := offset + w.parents.length + 2
    orientation := ?_
    witness := actual
    start_vertex := startTrace.symm
    position_trace := ?_
    span := ?_
    parents := ?_
    colliders := ?_
  }, rfl, rfl, rfl, terminalTrace⟩
  · exact Or.inl ⟨by omega, rfl, by omega⟩
  · refine Or.inl ⟨by omega, ?_⟩
    simpa only [actual, DiscriminatingWitness.vertices, finishTrace] using «trace»
  · exact ⟨fun _ => rfl, fun «impossible» => by omega⟩
  · intro i interior
    have lower : offset < i := by rcases interior with h | h <;> omega
    have upper : i < offset + (w.parents ++ [w.terminal]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      rcases interior with h | h <;> omega
    have result := (indexed_parent_route (mag D) c vertex w.prefix offset divided.1 i lower upper).1
    simpa only [finishTrace] using result
  · intro i interior
    have lower : offset < i := by rcases interior with h | h <;> omega
    have upper : i < offset + (w.parents ++ [w.terminal]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      rcases interior with h | h <;> omega
    exact (indexed_parent_route (mag D) c vertex w.prefix offset divided.1 i lower upper).2

theorem index_forward_occurrence {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) {a b c : X}
    (w : DiscriminatingWitness (mag D) a b c) (whole : List X)
    («trace» : Trace vertex 0 whole) (occurs : w.OccursOn whole) :
    ∃ offset, ∃ indexed : IndexedWitness D vertex (offset + w.parents.length + 1),
      indexed.start = offset ∧ indexed.before = offset + w.parents.length ∧
      indexed.finish = offset + w.parents.length + 2 ∧ indexed.finish < whole.length ∧
      vertex (offset + w.parents.length + 1) = b := by
  obtain ⟨front, back, equation⟩ := occurs
  rw [equation] at «trace»
  have outer := (trace_append vertex front (w.vertices ++ back) 0).mp
    (by simpa only [List.append_assoc] using «trace»)
  have inner := (trace_append vertex w.vertices back front.length).mp
    (by simpa only [Nat.zero_add] using outer.2)
  obtain ⟨indexed, start, before, finish, label⟩ := index_forward_witness D vertex w front.length inner.1
  refine ⟨front.length, indexed, start, before, finish, ?_, label⟩
  rw [equation, finish]
  simp only [DiscriminatingWitness.vertices, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  omega

end RestrictedCausal.IndexedDiscriminatingSections
