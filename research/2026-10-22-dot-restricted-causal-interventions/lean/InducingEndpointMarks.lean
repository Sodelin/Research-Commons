import DiscriminatingSeparatorStatus

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

A classical endpoint-incidence component of the remaining full selected-MAG
representation theorem. A tail at the first endpoint of an inducing route
forces ancestry to the other endpoint or selection. Thus a literal MAG
arrowhead cannot be silently replaced by a tail in the source path.
This is not, on its own, a full m-separation representation theorem.
-/

namespace RestrictedCausal.InducingSeparation

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection HPLTarget
open SourceSelection (AncestorOf)

universe u v w

/-- Starting with a head, follow arrows until the first collider or the
terminal. No shortest-path or ancestral-graph provider is assumed. -/
theorem head_route_reaches_collider_or_end {V : Type u} (G : MarkedGraph V)
    (laws : MixedLaws G) (C B : V → Prop)
    {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C B) p xs q) (hp : p.incoming = some .head) :
    ∃ z, Reach G p.vertex z ∧ (B z ∨ z = q.vertex) := by
  revert hp
  induction h with
  | nil p => intro _; exact ⟨p.vertex, ⟨[], .nil _⟩, Or.inr rfl⟩
  | @cons p next q rest hstep hrest ih =>
      intro hp
      obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
      cases outgoing with
      | head =>
          have hb : B p.vertex := by simpa [hp, ActiveAt] using hactive
          exact ⟨p.vertex, ⟨[], .nil _⟩, Or.inl hb⟩
      | tail =>
          have hin : incoming = .head := by
            cases incoming with
            | head => rfl
            | tail => exact (laws.no_tail_tail _ _ hedge).elim
          subst incoming
          obtain ⟨z, ⟨zs, hzs⟩, hz⟩ := ih hmark
          exact ⟨z, ⟨next.vertex :: zs, .cons hedge hzs⟩, hz⟩

/-- The initial arrow makes the return-to-first-endpoint alternative a real
directed cycle. The other two alternatives are exactly the literal tail flag.
The conditioning predicate is arbitrary; only the collider ancestor bound
is used, so the lemma applies before endpoint-activation shortcuts. -/
theorem first_tail_forces_flag {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X)
    (C B : SourceVertex X S L → Prop)
    (bound : ∀ a, B a → EndpointAncestor D x y a)
    {p q : Arrival (SourceVertex X S L)} {xs : List (Arrival (SourceVertex X S L))}
    (first : Directed (arrowGraph D.arrow) (Observed x) p.vertex)
    (hp : p.incoming = some .head)
    (rest : Route (Transition (arrowGraph D.arrow) C B) p xs q)
    (hq : q.vertex = Observed y) : TailFlag D x y := by
  obtain ⟨z, hpz, hz⟩ := head_route_reaches_collider_or_end
    (arrowGraph D.arrow) (original_arrow_mixed_laws D) C B rest hp
  have hxp : Reach (arrowGraph D.arrow) (Observed x) p.vertex :=
    ⟨[p.vertex], .cons first (.nil _)⟩
  rcases hz with hb | hend
  · obtain ⟨endpoint, hze, he⟩ := bound z hb
    have hpe := reach_trans hpz hze
    rcases he with hx | hy | hs
    · have back : Reach (arrowGraph D.arrow) p.vertex (Observed x) := by
        simpa only [hx] using hpe
      have equal := reach_antisymm_of_acyclic (arrowGraph D.arrow) (source_directed_acyclic D) hxp back
      have self : Directed (arrowGraph D.arrow) (Observed x) (Observed x) := by
        simpa only [equal] using first
      exact ((original_arrow_mixed_laws D).irreflexive _ _ _ self).elim
    · left
      have reached := reach_trans hxp hpe
      simpa only [hy] using reached
    · right
      rcases endpoint with ((a | s) | l)
      · exact hs.elim
      · exact ⟨s, reach_trans hxp hpe⟩
      · exact hs.elim
  · left
    have reached := reach_trans hxp hpz
    simpa only [hend, hq] using reached

theorem first_mark_head_of_not_tail_flag {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (noTail : ¬ TailFlag D x y)
    (C B : SourceVertex X S L → Prop)
    (bound : ∀ a, B a → EndpointAncestor D x y a)
    {p q : Arrival (SourceVertex X S L)} {xs : List (Arrival (SourceVertex X S L))}
    (outgoing incoming : Mark)
    (edge : (arrowGraph D.arrow).edge (Observed x) p.vertex outgoing incoming)
    (hp : p.incoming = some incoming)
    (rest : Route (Transition (arrowGraph D.arrow) C B) p xs q)
    (hq : q.vertex = Observed y) : outgoing = .head := by
  cases outgoing with
  | head => rfl
  | tail =>
      have hi : incoming = .head := (tail_edge_forward D.arrow edge).2
      subst incoming
      exact (noTail (first_tail_forces_flag D x y C B bound edge hp rest hq)).elim

/-- Reverse a route with a specified incoming mark at its former terminal.
The supplied terminal departure condition is exactly what the first reversed
step requires. The returned compatibility at the other end is also explicit. -/
theorem reverse_with_arrival {V : Type u} (G : MarkedGraph V)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (C A : V → Prop) {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C A) p xs q) (actual : Option Mark)
    (ready : match actual with
      | none => True
      | some outgoing => DepartureAllowed C A q.vertex q.incoming outgoing) :
    ∃ last ys, Route (Transition G C A) ⟨q.vertex, actual⟩ ys ⟨p.vertex, last⟩ ∧
      (match p.incoming with
      | none => True
      | some previous => DepartureAllowed C A p.vertex last previous) := by
  revert ready
  revert actual
  induction h with
  | nil p =>
      intro actual ready
      refine ⟨actual, [], .nil _, ?_⟩
      cases hm : p.incoming with
      | none => trivial
      | some previous =>
          cases actual with
          | none => trivial
          | some outgoing =>
              have hactive : ActiveAt C A p.vertex previous outgoing := by
                simpa only [DepartureAllowed, hm] using ready
              exact (activeAt_swap C A p.vertex previous outgoing).mp hactive
  | @cons p next q rest hstep hrest ih =>
      intro actual ready
      obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
      obtain ⟨last, ys, hy, hready⟩ := ih actual ready
      have backward : Transition G C A ⟨next.vertex, last⟩ ⟨p.vertex, some outgoing⟩ := by
        refine ⟨incoming, outgoing, symmetric _ _ _ _ hedge, rfl, ?_⟩
        simpa only [hmark] using hready
      refine ⟨some outgoing, ys ++ [⟨p.vertex, some outgoing⟩],
        hy.append (.cons backward (.nil _)), ?_⟩
      cases hm : p.incoming with
      | none => trivial
      | some previous =>
          have ha : ActiveAt C A p.vertex previous outgoing := by simpa only [hm] using hactive
          exact (activeAt_swap C A p.vertex previous outgoing).mp ha

theorem endpoint_ancestor_swap {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (a : SourceVertex X S L)
    (h : EndpointAncestor D x y a) : EndpointAncestor D y x a := by
  apply ancestor_mono (C := EndpointSelection x y) (fun v hv => ?_) h
  rcases hv with hx | hy | hs
  · exact Or.inr (Or.inl hx)
  · exact Or.inl hy
  · exact Or.inr (Or.inr hs)

/-- The terminal incidence obeys the same restriction. Reversal is performed
with the exact incoming mark supplied by the final edge, not with an arbitrary
or forgotten endpoint state. -/
theorem last_mark_head_of_not_tail_flag {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (noTail : ¬ TailFlag D y x)
    (C B : SourceVertex X S L → Prop)
    (bound : ∀ a, B a → EndpointAncestor D x y a)
    {p : Arrival (SourceVertex X S L)} {xs : List (Arrival (SourceVertex X S L))}
    (prefix : Route (Transition (arrowGraph D.arrow) C B) ⟨Observed x, none⟩ xs p)
    (outgoing incoming : Mark)
    (edge : (arrowGraph D.arrow).edge p.vertex (Observed y) outgoing incoming)
    (ready : DepartureAllowed C B p.vertex p.incoming outgoing) : incoming = .head := by
  obtain ⟨last, ys, reversed, _⟩ := reverse_with_arrival (arrowGraph D.arrow)
    (arrow_graph_symm D.arrow) C B prefix (some outgoing) ready
  exact first_mark_head_of_not_tail_flag D y x noTail C B
    (fun a ha => endpoint_ancestor_swap D x y a (bound a ha)) incoming outgoing
    (arrow_graph_symm D.arrow _ _ _ _ edge) rfl reversed rfl

end RestrictedCausal.InducingSeparation
