import WeakRouteNormalization

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The original-to-MAG direction, composed with the previously proved converse.
The proof maps a concretely normalized weak route, not an assumed source
adapter. Physical simplicity follows from its exact observed vertex trace.
The representation theorem is classical (Richardson--Spirtes), specialized
to the literal Hou--Park--Li DAG/selection-sink construction used here.
-/

namespace RestrictedCausal.WeakInducing

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open FramedWalk HPLTarget MAGLifting
open SourceSelection (AncestorOf)

universe u v w

noncomputable def endpointLabel {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : Mark := by
  classical
  exact if TailFlag D x y then .tail else .head

theorem endpointLabel_spec {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : EndpointMark D x y (endpointLabel D x y) := by
  classical
  by_cases flag : TailFlag D x y
  · exact Or.inl ⟨by simp [endpointLabel, flag], flag⟩
  · exact Or.inr ⟨by simp [endpointLabel, flag], flag⟩

theorem endpointLabel_head_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : endpointLabel D x y = .head ↔ ¬ TailFlag D x y := by
  classical
  by_cases flag : TailFlag D x y <;> simp [endpointLabel, flag]

theorem weak_edge_mag {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {«left» «right» : Mark} (h : (graph D).edge x y «left» «right») :
    (mag D).edge x y (endpointLabel D x y) (endpointLabel D y x) :=
  ⟨edge_inducing D h, endpointLabel_spec D x y, endpointLabel_spec D y x⟩

theorem normalized_join_active {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) {a b c : Arrival X}
    {«left» incoming outgoing «right» : Mark}
    («first» : (graph D).edge a.vertex b.vertex «left» incoming)
    (last : (graph D).edge b.vertex c.vertex outgoing «right»)
    (active : ActiveAt Z (Activated D Z) b.vertex incoming outgoing)
    (good : GoodJoin D Z a b c) :
    ActiveAt Z (AncestorOf (mag D) Z) b.vertex
      (endpointLabel D b.vertex a.vertex) (endpointLabel D b.vertex c.vertex) := by
  classical
  by_cases collider : endpointLabel D b.vertex a.vertex = .head ∧
      endpointLabel D b.vertex c.vertex = .head
  · simp only [ActiveAt, if_pos collider]
    have noLeftFlag := (endpointLabel_head_iff D b.vertex a.vertex).mp collider.1
    have noRightFlag := (endpointLabel_head_iff D b.vertex c.vertex).mp collider.2
    have inHead := marked_inducing_right_head D a.vertex b.vertex «first».2 noLeftFlag
    have outHead := marked_inducing_left_head D b.vertex c.vertex last.2 noRightFlag
    have sourceActive : Activated D Z b.vertex := by simpa [ActiveAt, inHead, outHead] using active
    have notSelected : ¬ SelectionAncestor D b.vertex := fun hs => noLeftFlag (Or.inr hs)
    exact (collider_ancestry_iff_not_selected D Z b.vertex notSelected).mp sourceActive
  · simp only [ActiveAt, if_neg collider]
    intro conditioned
    obtain ⟨leftFlag, rightFlag⟩ := good conditioned
    exact collider ⟨(endpointLabel_head_iff D b.vertex a.vertex).mpr leftFlag,
      (endpointLabel_head_iff D b.vertex c.vertex).mpr rightFlag⟩

theorem map_after_first {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop)
    {b q : Arrival X} {xs : List (Arrival X)}
    (route : Route (Transition (graph D) Z (Activated D Z)) b xs q) :
    ∀ (a : Arrival X) («left» incoming : Mark), (graph D).edge a.vertex b.vertex «left» incoming →
      b.incoming = some incoming → AllTriples (GoodJoin D Z) (a :: b :: xs) →
      ∃ last ys, Route (Transition (mag D) Z (AncestorOf (mag D) Z))
        ⟨b.vertex, some (endpointLabel D b.vertex a.vertex)⟩ ys ⟨q.vertex, last⟩ ∧
        ys.map Arrival.vertex = xs.map Arrival.vertex := by
  induction route with
  | nil b =>
      intro a «left» incoming edge mark good
      exact ⟨some (endpointLabel D b.vertex a.vertex), [], .nil _, rfl⟩
  | @cons b c q rest step tail ih =>
      intro a «left» incoming firstEdge mark good
      obtain ⟨outgoing, nextIncoming, nextEdge, nextMark, active⟩ := step
      have atB : ActiveAt Z (Activated D Z) b.vertex incoming outgoing := by
        simpa only [mark] using active
      have magActive := normalized_join_active D Z firstEdge nextEdge atB good.1
      obtain ⟨last, ys, mappedTail, sameVertices⟩ := ih b outgoing nextIncoming nextEdge nextMark good.2
      refine ⟨last, ⟨c.vertex, some (endpointLabel D c.vertex b.vertex)⟩ :: ys,
        .cons ?_ mappedTail, ?_⟩
      · exact ⟨endpointLabel D b.vertex c.vertex, endpointLabel D c.vertex b.vertex,
          weak_edge_mag D nextEdge, rfl, magActive⟩
      · simpa only [List.map_cons, sameVertices]

theorem good_weak_route_is_mag {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X)
    {last : Option Mark} {xs : List (Arrival X)}
    (route : Route (Transition (graph D) Z (Activated D Z)) ⟨x, none⟩ xs ⟨y, last⟩)
    (nodup : ((⟨x, none⟩ :: xs).map Arrival.vertex).Nodup)
    (good : AllTriples (GoodJoin D Z) (⟨x, none⟩ :: xs)) : ActiveConnection (mag D) Z x y := by
  cases route with
  | nil => exact ⟨none, [], .nil _, nodup⟩
  | @cons p b q rest «first» tail =>
      obtain ⟨«left», incoming, firstEdge, mark, _⟩ := «first»
      obtain ⟨magLast, ys, mappedTail, sameVertices⟩ :=
        map_after_first D Z tail p «left» incoming firstEdge mark good
      refine ⟨magLast, ⟨b.vertex, some (endpointLabel D b.vertex x)⟩ :: ys,
        .cons ?_ mappedTail, ?_⟩
      · exact ⟨endpointLabel D x b.vertex, endpointLabel D b.vertex x,
          weak_edge_mag D firstEdge, rfl, trivial⟩
      · simpa only [List.map_cons, sameVertices] using nodup

/-- Every original selected active path produces an active path in the
literal marked MAG. No independent slice realization or finite source bound
is substituted. The initial and terminal conditioning exclusions are not
needed for this direction, but are retained in the final biconditional. -/
theorem original_connection_implies_mag {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X)
    (h : ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y)) :
    ActiveConnection (mag D) Z x y := by
  obtain ⟨last, xs, weakRoute, nodup⟩ := original_connection_is_weak D Z x y h
  obtain ⟨ys, normalized, normalizedNodup, good, _⟩ := normalize_weak_route D Z weakRoute nodup
  exact good_weak_route_is_mag D Z x y normalized normalizedNodup good

/-- Complete classical selected-DAG/MAG representation, at the unchanged
all-observed target. This is a source-only proof term, not a Lean certificate. -/
theorem selected_mag_connection_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) (hx : ¬ Z x) (hy : ¬ Z y) :
    ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y) ↔
      ActiveConnection (mag D) Z x y :=
  ⟨original_connection_implies_mag D Z x y, mag_connection_implies_original D Z x y hx hy⟩

end RestrictedCausal.WeakInducing
