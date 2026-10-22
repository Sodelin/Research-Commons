import ClosedColliderWalks

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Intermediate marked edges are actual inducing walks in the original DAG.
They retain the incidences needed for contraction. Their graph is not the
reported target. Every edge is proved to be a literal MAG adjacency, and a
conditioned join that loses its collider mark can be merged explicitly.
-/

namespace RestrictedCausal.WeakInducing

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open FramedWalk ClosedColliderWalks HPLTarget
open SourceSelection (AncestorOf)

universe u v w

def graph {X : Type u} {S : Type v} {L : Type w} (D : SourceDAG X S L) : MarkedGraph X where
  edge x y mx my := x ≠ y ∧ MarkedRoute (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y)
    (Observed x) (Observed y) mx my

def Activated {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x : X) : Prop :=
  AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) (Observed x)

theorem edge_inducing {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {mx my : Mark} (h : (graph D).edge x y mx my) :
    InducingPath D x y := marked_inducing_walk_is_path D h.1 h.2

theorem edge_symmetric {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {mx my : Mark} (h : (graph D).edge x y mx my) :
    (graph D).edge y x my mx :=
  ⟨h.1.symm, (h.2.reverse (arrow_graph_symm D.arrow)).mono
    (fun _ h => h) (endpoint_ancestor_swap D x y)⟩

theorem endpoint_ancestor_enlarge {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y a b : X}
    (hx : EndpointAncestor D a b (Observed x)) (hy : EndpointAncestor D a b (Observed y)) :
    ∀ q, EndpointAncestor D x y q → EndpointAncestor D a b q := by
  intro q h
  apply ancestor_idempotent
  apply ancestor_mono (C := EndpointSelection x y) (A := EndpointAncestor D a b) ?_ h
  intro r hr
  rcases hr with eq | eq | selected
  · exact eq.symm ▸ hx
  · exact eq.symm ▸ hy
  · exact ⟨r, ⟨[], .nil r⟩, Or.inr (Or.inr selected)⟩

theorem endpoint_self_left {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : EndpointAncestor D x y (Observed x) :=
  ⟨Observed x, ⟨[], .nil _⟩, Or.inl rfl⟩

theorem endpoint_self_right {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : EndpointAncestor D x y (Observed y) :=
  ⟨Observed y, ⟨[], .nil _⟩, Or.inr (Or.inl rfl)⟩

theorem tail_flag_middle_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x middle y : X)
    (h : TailFlag D middle x ∨ TailFlag D middle y) : EndpointAncestor D x y (Observed middle) := by
  rcases h with (reach | ⟨s, reach⟩) | (reach | ⟨s, reach⟩)
  · exact ⟨Observed x, reach, Or.inl rfl⟩
  · exact ⟨.inl (.inr s), reach, Or.inr (Or.inr trivial)⟩
  · exact ⟨Observed y, reach, Or.inr (Or.inl rfl)⟩
  · exact ⟨.inl (.inr s), reach, Or.inr (Or.inr trivial)⟩

/-- The actual two-edge merge preserves the two outer raw incidences. The
middle vertex is a collider on the raw concatenation and ancestral to an
outer endpoint or selection. Repeated original vertices are allowed here;
`edge_inducing` removes them with the proved closed-ancestor reduction. -/
theorem merge_collider_edges {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x middle y : X} {left right : Mark}
    (hne : x ≠ y) (first : (graph D).edge x middle left .head)
    (last : (graph D).edge middle y .head right)
    (flag : TailFlag D middle x ∨ TailFlag D middle y) : (graph D).edge x y left right := by
  have middleAncestor := tail_flag_middle_ancestor D x middle y flag
  have firstWalk := first.2.mono (fun _ h => h)
    (endpoint_ancestor_enlarge D (endpoint_self_left D x y) middleAncestor)
  have lastWalk := last.2.mono (fun _ h => h)
    (endpoint_ancestor_enlarge D middleAncestor (endpoint_self_right D x y))
  refine ⟨hne, firstWalk.append lastWalk ?_⟩
  simpa [ActiveAt] using middleAncestor

theorem retained_edge_marked_walk {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (A : SourceVertex X S L → Prop)
    (latent : List L) {a b : SourceVertex X S L} {left right : Mark}
    (h : NoncolliderRoute (arrowGraph D.arrow) a left
      (latent.map (fun l => Sum.inr l : L → SourceVertex X S L)) b right) :
    MarkedRoute (arrowGraph D.arrow) Nonlatent A a b left right := by
  induction latent generalizing a left with
  | nil =>
      cases h with
      | single edge => exact ⟨b, right, [], edge, .nil _⟩
  | cons l ls ih =>
      cases h with
      | @step _ _ _ _ incoming outgoing _ _ edge noncollider tail =>
          have rest := ih tail
          have ready : ActiveAt Nonlatent A (.inr l) incoming outgoing := by
            simp [ActiveAt, noncollider, Nonlatent]
          obtain ⟨xs, route⟩ := rest.with_arrival ready
          exact ⟨.inr l, incoming, xs, edge, route⟩

theorem projected_edge_marked_walk {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (A : SourceVertex X S L → Prop)
    {a b : Sum X S} {left right : Mark} (h : (projection D).edge a b left right) :
    MarkedRoute (arrowGraph D.arrow) Nonlatent A (.inl a) (.inl b) left right := by
  obtain ⟨_, latent, route⟩ := h
  exact retained_edge_marked_walk D A latent route

theorem observed_projected_edge_weak {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {left right : Mark}
    (h : (extracted D).observed.edge x y left right) : (graph D).edge x y left right := by
  refine ⟨?_, projected_edge_marked_walk D (EndpointAncestor D x y) h⟩
  intro eq
  subst y
  exact (extracted_observed_laws D).irreflexive x left right h

theorem selected_endpoint_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (s : S) : EndpointAncestor D x y (.inl (.inr s)) :=
  ⟨.inl (.inr s), ⟨[], .nil _⟩, Or.inr (Or.inr trivial)⟩

theorem selection_component_inducing_route {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) {s t : S} {xs : List S}
    (h : Route (extracted D).selectionEdge s xs t) :
    ∃ ys, Route (Transition (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y))
      ⟨.inl (.inr s), some .head⟩ ys ⟨.inl (.inr t), some .head⟩ := by
  induction h with
  | nil s => exact ⟨[], .nil _⟩
  | @cons s t r xs edge tail ih =>
      have walk := projected_edge_marked_walk D (EndpointAncestor D x y) edge
      have ready : ActiveAt Nonlatent (EndpointAncestor D x y) (.inl (.inr s)) .head .head := by
        simpa [ActiveAt] using selected_endpoint_ancestor D x y s
      obtain ⟨front, frontRoute⟩ := walk.with_arrival ready
      obtain ⟨back, backRoute⟩ := ih
      exact ⟨front ++ back, frontRoute.append backRoute⟩

theorem selection_bridge_weak {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {left right : Mark}
    (h : SourceSelection.Bridge (extracted D) x left y right) : (graph D).edge x y left right := by
  obtain ⟨hne, s, t, firstEdge, ⟨component, componentRoute⟩, lastEdge⟩ := h
  have firstWalk := projected_edge_marked_walk D (EndpointAncestor D x y) firstEdge
  have lastWalk := projected_edge_marked_walk D (EndpointAncestor D x y)
    (projection_symm D (.inl y) (.inr t) right .head lastEdge)
  obtain ⟨middle, middleRoute⟩ := selection_component_inducing_route D x y componentRoute
  have ready : ActiveAt Nonlatent (EndpointAncestor D x y) (.inl (.inr t)) .head .head := by
    simpa [ActiveAt] using selected_endpoint_ancestor D x y t
  obtain ⟨last, lastRoute⟩ := lastWalk.with_arrival ready
  obtain ⟨first, firstIncoming, prefix, edge, prefixRoute⟩ := firstWalk
  exact ⟨hne, first, firstIncoming, prefix ++ middle ++ last, edge,
    (prefixRoute.append middleRoute).append lastRoute⟩

end RestrictedCausal.WeakInducing
