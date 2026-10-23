import ClosestFirstArrow

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration, execution or kernel check.

Transfer every collider's conditioning ancestry on an actual closest path.
The first arrow is obtained from the preceding two-boundary proof; it is
not a premise. An induction on the real arrival route retains the WHOLE
original closest-path trace while moving the split through that route.
Classical attribution: Ali--Richardson--Spirtes (2009), Corollary 3.27 and
the sufficiency argument following it. No novelty is claimed.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing OriginalProjection
open IndexedDiscriminatingSections
open SourceSelection (AncestorOf)

universe u v w

theorem closest_collider_ancestry {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (H : MarkedGraph X) (lawsH : AncestralLaws H)
    (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent (mag D) a b ↔ Adjacent H a b)
    (shared : SharedSeparators (mag D) H)
    (Z : X → Prop) (x y : X)
    {b c : Arrival X} {prefix suffix : List (Arrival X)} {last : Option Mark}
    (before : Route (RealStep (mag D) Z) ⟨x, none⟩ prefix b)
    (bc : RealStep (mag D) Z b c)
    (following : Route (RealStep (mag D) Z) c suffix ⟨y, last⟩)
    (closest : Closest (mag D) Z x y ((prefix ++ (c :: suffix)).map Arrival.vertex))
    (notStart : ¬ Z x) (notEnd : ¬ Z y)
    (headB : b.incoming = some .head) (atB : ColliderStep (mag D) b c)
    (sourceAncestor : AncestorOf (mag D) Z b.vertex) :
    AncestorOf H Z b.vertex := by
  obtain ⟨vertices, finish, path, _⟩ :=
    minimum_directed_path_exists (mag D) Z b.vertex sourceAncestor
  cases vertices with
  | nil =>
      have same : finish = b.vertex := by cases path.route; rfl
      exact ⟨b.vertex, ⟨[], .nil _⟩, same ▸ path.endpoint⟩
  | cons d rest =>
      have first := closest_collider_first_arrow D H lawsH singleH skeleton shared
        Z x y d before bc following closest notStart notEnd headB atB path
      exact (minimum_directed_path_transfers_from_first (mag D) H
        (literal_mag_valid D).1 lawsH (mag_single_edges D) singleH
        skeleton shared Z path first).2

/-- The prefix is extended at every recursive step, so `closest` always
refers to the same COMPLETE original path. No local subpath is declared
closest and no independent replacement realization is chosen. -/
theorem closest_route_triples_transfer {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (H : MarkedGraph X) (lawsH : AncestralLaws H)
    (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent (mag D) a b ↔ Adjacent H a b)
    (shared : SharedSeparators (mag D) H) (Z : X → Prop) (x : X)
    {p q : Arrival X} {remaining : List (Arrival X)}
    (route : Route (RealStep (mag D) Z) p remaining q) :
    ∀ (prefix : List (Arrival X)),
      Route (RealStep (mag D) Z) ⟨x, none⟩ prefix p →
      Closest (mag D) Z x q.vertex ((prefix ++ remaining).map Arrival.vertex) →
      ¬ Z x → ¬ Z q.vertex →
      ∀ (a : X) (left incoming : Mark),
        (mag D).edge a p.vertex left incoming → p.incoming = some incoming →
        AllTriples (fun a b c => Collider (mag D) a b c ↔ Collider H a b c)
          (a :: p.vertex :: remaining.map Arrival.vertex) →
        AllTriples (TripleActive H Z) (a :: p.vertex :: remaining.map Arrival.vertex) := by
  induction route with
  | nil p => intro _ _ _ _ _ _ _ _ _ _ _; trivial
  | @cons p next q rest step tail ih =>
      intro prefix before closest notStart notEnd a left incoming first mark invariant
      obtain ⟨outgoing, received, edge, nextMark, active⟩ := step
      have atP : ActiveAt Z (AncestorOf (mag D) Z) p.vertex incoming outgoing := by
        simpa only [mark] using active
      have sourceActive := (triple_active_iff_marks (mag D) (mag_single_edges D) Z
        a p.vertex next.vertex left incoming outgoing received first edge).mpr atP
      have targetActive : TripleActive H Z a p.vertex next.vertex := by
        constructor
        · intro targetCollider
          have sourceCollider := invariant.1.mpr targetCollider
          have heads := (collider_iff_chosen_marks (mag D) (mag_single_edges D)
            a p.vertex next.vertex left incoming outgoing received first edge).mp sourceCollider
          have headP : p.incoming = some .head := mark.trans (congrArg some heads.1)
          have colliderStep : ColliderStep (mag D) p next :=
            ⟨outgoing, received, edge, nextMark, by simpa only [mark] using heads⟩
          exact closest_collider_ancestry D H lawsH singleH skeleton shared
            Z x q.vertex before ⟨outgoing, received, edge, nextMark, active⟩ tail
            closest notStart notEnd headP colliderStep (sourceActive.1 sourceCollider)
        · intro targetNoncollider
          exact sourceActive.2 (fun sourceCollider => targetNoncollider (invariant.1.mp sourceCollider))
      have extended : Route (RealStep (mag D) Z) ⟨x, none⟩ (prefix ++ [next]) next :=
        before.append (.cons ⟨outgoing, received, edge, nextMark, active⟩ (.nil _))
      have sameClosest : Closest (mag D) Z x q.vertex
          (((prefix ++ [next]) ++ rest).map Arrival.vertex) := by
        simpa only [List.append_assoc, List.singleton_append] using closest
      exact ⟨targetActive, ih (prefix ++ [next]) extended sameClosest notStart notEnd
        p.vertex outgoing received edge nextMark invariant.2⟩

theorem closest_path_transfers {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (H : MarkedGraph X) (lawsH : AncestralLaws H)
    (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent (mag D) a b ↔ Adjacent H a b)
    (shared : SharedSeparators (mag D) H)
    (Z : X → Prop) (x y : X) {xs : List X}
    (closest : Closest (mag D) Z x y xs) (notStart : ¬ Z x) (notEnd : ¬ Z y) :
    Path H Z x y xs := by
  have invariant := shortest_path_status_invariant D H lawsH singleH skeleton shared
    Z x y closest.1 notStart notEnd
  obtain ⟨last, states, route, trace, _⟩ :=
    vertex_path_realization (mag D) (mag_single_edges D) Z x y closest.1.1
  have allActive : AllTriples (TripleActive H Z) (x :: states.map Arrival.vertex) := by
    cases route with
    | nil => trivial
    | @cons p next q rest step tail =>
        obtain ⟨left, incoming, edge, mark, active⟩ := step
        have sourceClosest : Closest (mag D) Z x y
            (([next] ++ rest).map Arrival.vertex) := by
          simpa only [List.singleton_append, trace] using closest
        have localInvariant : AllTriples
            (fun a b c => Collider (mag D) a b c ↔ Collider H a b c)
            (x :: next.vertex :: rest.map Arrival.vertex) := by
          simpa only [← trace, List.map_cons] using invariant
        exact closest_route_triples_transfer D H lawsH singleH skeleton shared Z x tail
          [next] (.cons ⟨left, incoming, edge, mark, active⟩ (.nil _))
          sourceClosest notStart notEnd x left incoming edge mark localInvariant
  refine ⟨?_, closest.1.1.2.1, ?_⟩
  · simpa only [List.map_id] using
      closest.1.1.1.map id (by intro a b adjacent; exact (skeleton a b).mp adjacent)
  · simpa only [trace] using allActive

end RestrictedCausal.VertexActivePaths
