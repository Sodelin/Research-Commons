import IntervalDependency
import WeakInducingEdges

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The inducing-chain obstruction needed by the discriminating-interval proof.
For the literal MAG of an arbitrary original source DAG, a collider chain
whose internal vertices are ancestors of its endpoints forces adjacency.
The proof expands all its edges into the SAME original DAG, concatenates
with the actual head incidences, and erases loops only in that DAG. Thus it
does not apply a no-tail-tail reduction to a selected MAG or assume a MAG
representation theorem. This is classical ancestral-graph geometry, not a
novel claim; see Ali--Richardson--Spirtes (2009), Lemmas 3.13--3.15.
-/

namespace RestrictedCausal.LiteralMAGInducingChains

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation HPLTarget FramedWalk ClosedColliderWalks WeakInducing
open DiscriminatingStatus AncestralShortcutGeometry
open SourceSelection (AncestorOf)

universe u v w

def Endpoints {X : Type u} (x y q : X) : Prop := q = x ∨ q = y

abbrev ColliderChainStep {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) :=
  Transition (mag D) (fun _ => True) (AncestorOf (mag D) (Endpoints x y))

theorem endpoint_ancestry_lifts_at_head {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) {q r : X} {m : Mark}
    (head : (mag D).edge q r .head m)
    (ancestor : AncestorOf (mag D) (Endpoints x y) q) :
    EndpointAncestor D x y (Observed q) := by
  obtain ⟨endpoint, ⟨vertices, directed⟩, atEnd⟩ := ancestor
  have lifted := mag_directed_route_lifts D directed (head_not_source_ancestor D head).2
  rcases atEnd with eq | eq
  · subst endpoint
    exact ⟨Observed x, lifted, Or.inl rfl⟩
  · subst endpoint
    exact ⟨Observed y, lifted, Or.inr (Or.inl rfl)⟩

/-- A reached nonterminal chain vertex is a head-head collider. The terminal
vertex is y itself. These are the only two cases, so every expansion endpoint
has the source-level ancestry needed to enlarge its edge's inducing walk. -/
theorem reached_chain_vertex_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) {p q : Arrival X} {xs : List (Arrival X)}
    (route : Route (ColliderChainStep D x y) p xs q) (lastVertex : q.vertex = y)
    (arrived : ∃ m, p.incoming = some m) : EndpointAncestor D x y (Observed p.vertex) := by
  cases route with
  | nil p => simpa only [lastVertex] using endpoint_self_right D x y
  | @cons p «next» q rest step tail =>
      obtain ⟨outgoing, incoming, edge, mark, active⟩ := step
      obtain ⟨previous, previousMark⟩ := arrived
      have atP : ActiveAt (fun _ : X => True) (AncestorOf (mag D) (Endpoints x y))
          p.vertex previous outgoing := by simpa only [previousMark] using active
      obtain ⟨previousHead, outgoingHead⟩ :=
        ActiveWalkReduction.conditioned_active_heads True.intro atP
      have ancestor : AncestorOf (mag D) (Endpoints x y) p.vertex := by
        simpa only [previousHead, outgoingHead, ActiveAt] using atP
      exact endpoint_ancestry_lifts_at_head D x y (outgoingHead ▸ edge) ancestor

def TracksArrival {X : Type u} (p : Arrival X) (actual : Option Mark) : Prop :=
  (p.incoming = none → actual = none) ∧
    (p.incoming = some .head → actual = some .head)

/-- Expand a collider chain while retaining a real original-DAG prefix.
The source ancestry and the incoming-head invariant are proved at each step.
No separate realization of different edges, regimes, or indicators is used. -/
theorem expand_chain_with_prefix {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) {p q : Arrival X} {xs : List (Arrival X)}
    (chain : Route (ColliderChainStep D x y) p xs q) (lastVertex : q.vertex = y) :
    ∀ (actual : Option Mark) («prefix» : List (Arrival (SourceVertex X S L))),
      Route (Transition (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y))
        ⟨Observed x, none⟩ «prefix» ⟨Observed p.vertex, actual⟩ →
      EndpointAncestor D x y (Observed p.vertex) → TracksArrival p actual →
      ∃ last vertices,
        Route (Transition (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y))
          ⟨Observed x, none⟩ vertices ⟨Observed y, last⟩ := by
  revert lastVertex
  induction chain with
  | nil p =>
      intro lastVertex actual «prefix» lifted ancestor tracks
      exact ⟨actual, «prefix», by simpa only [lastVertex] using lifted⟩
  | @cons p «next» q rest step tail ih =>
      intro lastVertex actual «prefix» lifted ancestor tracks
      obtain ⟨outgoing, incoming, edge, mark, active⟩ := step
      have nextAncestor := reached_chain_vertex_ancestor D x y tail lastVertex ⟨incoming, mark⟩
      obtain ⟨rawLeft, rawRight, walk⟩ := inducing_marked_route D p.vertex «next».vertex edge.1
      have leftHead : outgoing = .head → rawLeft = .head := by
        intro head
        exact marked_inducing_left_head D p.vertex «next».vertex walk
          ((endpoint_head_iff D p.vertex «next».vertex).mp (head ▸ edge.2.1))
      have rightHead : incoming = .head → rawRight = .head := by
        intro head
        exact marked_inducing_right_head D p.vertex «next».vertex walk
          ((endpoint_head_iff D «next».vertex p.vertex).mp (head ▸ edge.2.2))
      have expanded := walk.mono (fun _ h => h) (endpoint_ancestor_enlarge D ancestor nextAncestor)
      have ready : DepartureAllowed Nonlatent (EndpointAncestor D x y)
          (Observed p.vertex) actual rawLeft := by
        cases previousMark : p.incoming with
        | none => rw [tracks.1 previousMark]; trivial
        | some previous =>
            have atP : ActiveAt (fun _ : X => True) (AncestorOf (mag D) (Endpoints x y))
                p.vertex previous outgoing := by simpa only [previousMark] using active
            obtain ⟨previousHead, outgoingHead⟩ :=
              ActiveWalkReduction.conditioned_active_heads True.intro atP
            have actualHead := tracks.2 (previousMark.trans (congrArg some previousHead))
            simpa only [DepartureAllowed, actualHead, leftHead outgoingHead, ActiveAt] using ancestor
      obtain ⟨«first», firstIncoming, remainder, firstEdge, remainderRoute⟩ := expanded
      have copied : Transition (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y)
          ⟨Observed p.vertex, actual⟩ ⟨«first», some firstIncoming⟩ :=
        ⟨rawLeft, firstIncoming, firstEdge, rfl, ready⟩
      have nextTracks : TracksArrival «next» (some rawRight) := by
        constructor
        · intro none
          have «impossible» := none.symm.trans mark
          cases «impossible»
        · intro head
          have incomingHead : incoming = .head := Option.some.inj (mark.symm.trans head)
          exact congrArg some (rightHead incomingHead)
      exact ih lastVertex (some rawRight) («prefix» ++ (⟨«first», some firstIncoming⟩ :: remainder))
        (lifted.append (.cons copied remainderRoute)) nextAncestor nextTracks

theorem collider_chain_inducing {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (different : x ≠ y)
    {last : Option Mark} {vertices : List (Arrival X)}
    (chain : Route (ColliderChainStep D x y) ⟨x, none⟩ vertices ⟨y, last⟩) :
    InducingPath D x y := by
  have tracks : TracksArrival (⟨x, none⟩ : Arrival X) none :=
    ⟨fun _ => rfl, fun «impossible» => by cases «impossible»⟩
  obtain ⟨rawLast, rawVertices, rawRoute⟩ := expand_chain_with_prefix D x y chain rfl none []
    (.nil _) (endpoint_self_left D x y) tracks
  obtain ⟨terminal, simpleVertices, simple, endpoint, nodup⟩ := closed_walk_to_simple
    (arrowGraph D.arrow) (original_arrow_mixed_laws D) Nonlatent (EndpointAncestor D x y)
    (ancestor_backward_closed (arrowGraph D.arrow) (EndpointSelection x y)) rawRoute
  have terminalEq : terminal = ⟨Observed y, terminal.incoming⟩ := Arrival.eq_of_fields endpoint rfl
  rw [terminalEq] at simple
  exact ⟨different, terminal.incoming, simpleVertices, simple, nodup⟩

theorem collider_chain_forces_adjacency {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (different : x ≠ y)
    {last : Option Mark} {vertices : List (Arrival X)}
    (chain : Route (ColliderChainStep D x y) ⟨x, none⟩ vertices ⟨y, last⟩) :
    Adjacent (mag D) x y :=
  (mag_adjacent_iff_inducing D x y).mpr (collider_chain_inducing D x y different chain)

theorem parent_prefix_is_endpoint_chain {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) {p q : Arrival X} {xs : List (Arrival X)}
    (route : Route (ColliderParentStep (mag D) y) p xs q) :
    Route (ColliderChainStep D x y) p xs q := by
  induction route with
  | nil p => exact .nil p
  | @cons p «next» q rest step tail ih =>
      obtain ⟨outgoing, incoming, edge, mark, parent⟩ := step
      refine .cons ⟨outgoing, incoming, edge, mark, ?_⟩ ih
      cases previousMark : p.incoming with
      | none => trivial
      | some previous =>
          have details : previous = .head ∧ outgoing = .head ∧ Directed (mag D) p.vertex y := by
            simpa only [previousMark] using parent
          have ancestor : AncestorOf (mag D) (Endpoints x y) p.vertex :=
            ⟨y, ⟨[y], .cons details.2.2 (.nil y)⟩, Or.inr rfl⟩
          simpa only [previousMark, details.1, details.2.1, ActiveAt] using ancestor

/-- The terminal collider on a discriminating path cannot be an ancestor of
that path's nonadjacent start. Otherwise its complete collider chain expands
to an inducing path, contradicting the path's actual nonedge. This is the
boundary case in excluding mutually dependent discriminating intervals. -/
theorem discriminating_collider_not_reach_start {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {a b c : X}
    (w : VertexActivePaths.DiscriminatingWitness (mag D) a b c)
    (collider : Collider (mag D) a b c) : ¬ Reach (mag D) b w.start := by
  intro reach
  obtain ⟨firstLeft, lastRight, firstEdge, lastEdge⟩ := collider
  obtain ⟨outgoing, incoming, parentEdge, mark, _⟩ := w.last_parent_step
  have aligned : (mag D).edge a b outgoing incoming := by
    simpa only [w.before_vertex, w.terminal_vertex] using parentEdge
  have head : incoming = .head :=
    (mag_single_edges D a b outgoing incoming firstLeft .head aligned firstEdge).2
  have terminalHead := mark.trans (congrArg some head)
  have ancestor : AncestorOf (mag D) (Endpoints w.start c) b :=
    ⟨w.start, reach, Or.inl rfl⟩
  have lastStep : ColliderChainStep D w.start c w.terminal ⟨c, some lastRight⟩ := by
    refine ⟨.head, lastRight, ?_, rfl, ?_⟩
    · simpa only [w.terminal_vertex] using lastEdge
    · simpa only [terminalHead, w.terminal_vertex, ActiveAt] using ancestor
  have chain := (parent_prefix_is_endpoint_chain D w.start c w.prefix).append
    (.cons lastStep (.nil _))
  have different : w.start ≠ c := by
    intro equal
    have simple : (w.start :: ((w.parents ++ [w.terminal]).map Arrival.vertex ++ [c])).Nodup := by
      simpa only [List.map_cons, List.cons_append] using w.simple
    apply (List.nodup_cons.mp simple).1
    apply List.mem_append.mpr
    exact Or.inr (by simpa only [List.mem_singleton] using equal)
  exact w.nonadjacent (collider_chain_forces_adjacency D w.start c different chain)

end RestrictedCausal.LiteralMAGInducingChains
