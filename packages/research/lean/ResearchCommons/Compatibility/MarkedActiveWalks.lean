import InducingEndpointMarks


/- Pinned-context proof variant: expose the SAME identity maps/simplification,
or eliminate the existing impossible Sum equality. All original theorem and
source/graph/conditioning hypotheses and conclusion semantics remain. -/
/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Endpoint-marked walks for the actual full MAG-representation dependency.
Concatenation checks the exact activity at the joining vertex. Reversal
preserves both endpoint incidences. Neither a graph adapter nor a full
MAG separation equivalence is assumed.
-/

namespace RestrictedCausal.FramedWalk

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation RefinedSeparator

universe u v w

/-- A positive-length marked route. Endpoints have no activity requirement;
all internal departures use the specified actual conditioning/ancestor data.
Repeats are allowed so edge realizations can be concatenated before genuine
source-DAG physical loop reduction. -/
def MarkedRoute {V : Type u} (G : MarkedGraph V) (C A : V → Prop)
    (x y : V) («left» «right» : Mark) : Prop :=
  ∃ «first» incoming rest, G.edge x «first» «left» incoming ∧
    Route (Transition G C A) ⟨«first», some incoming⟩ rest ⟨y, some «right»⟩

theorem MarkedRoute.to_route {V : Type u} {G : MarkedGraph V} {C A : V → Prop}
    {x y : V} {«left» «right» : Mark} (h : MarkedRoute G C A x y «left» «right») :
    ∃ xs, Route (Transition G C A) ⟨x, none⟩ xs ⟨y, some «right»⟩ := by
  obtain ⟨«first», incoming, rest, hedge, hrest⟩ := h
  exact ⟨⟨«first», some incoming⟩ :: rest,
    .cons ⟨«left», incoming, hedge, rfl, trivial⟩ hrest⟩

theorem MarkedRoute.with_arrival {V : Type u} {G : MarkedGraph V} {C A : V → Prop}
    {x y : V} {«left» «right» incoming : Mark} (h : MarkedRoute G C A x y «left» «right»)
    (ready : ActiveAt C A x incoming «left») :
    ∃ xs, Route (Transition G C A) ⟨x, some incoming⟩ xs ⟨y, some «right»⟩ := by
  obtain ⟨«first», nextIncoming, rest, hedge, hrest⟩ := h
  exact ⟨⟨«first», some nextIncoming⟩ :: rest,
    .cons ⟨«left», nextIncoming, hedge, rfl, ready⟩ hrest⟩

theorem MarkedRoute.append_last {V : Type u} {G : MarkedGraph V} {C A : V → Prop}
    {x y z : V} {«left» middle outgoing «right» : Mark}
    (h : MarkedRoute G C A x y «left» middle) (edge : G.edge y z outgoing «right»)
    (ready : ActiveAt C A y middle outgoing) : MarkedRoute G C A x z «left» «right» := by
  obtain ⟨«first», incoming, rest, hedge, hrest⟩ := h
  refine ⟨«first», incoming, rest ++ [⟨z, some «right»⟩], hedge, ?_⟩
  exact hrest.append (.cons ⟨outgoing, «right», edge, rfl, ready⟩ (.nil _))

theorem MarkedRoute.append {V : Type u} {G : MarkedGraph V} {C A : V → Prop}
    {x y z : V} {«left» incoming outgoing «right» : Mark}
    («first» : MarkedRoute G C A x y «left» incoming)
    (last : MarkedRoute G C A y z outgoing «right»)
    (ready : ActiveAt C A y incoming outgoing) : MarkedRoute G C A x z «left» «right» := by
  obtain ⟨«next», nextIncoming, tail, edge, ht⟩ := «first»
  obtain ⟨rest, hr⟩ := last.with_arrival ready
  exact ⟨«next», nextIncoming, tail ++ rest, edge, ht.append hr⟩

theorem reverse_after_first {V : Type u} (G : MarkedGraph V)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (C A : V → Prop) {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C A) p xs q) :
    ∀ (x : V) («left» incoming «right» : Mark), G.edge x p.vertex «left» incoming →
      p.incoming = some incoming → q.incoming = some «right» →
      MarkedRoute G C A q.vertex x «right» «left» := by
  induction h with
  | nil p =>
      intro x «left» incoming «right» edge hp hq
      have eq : incoming = «right» := Option.some.inj (hp.symm.trans hq)
      subst incoming
      exact ⟨x, «left», [], symmetric _ _ _ _ edge, .nil _⟩
  | @cons p «next» q rest hstep hrest ih =>
      intro x «left» incoming «right» edge hp hq
      obtain ⟨outgoing, nextIncoming, hedge, hmark, hactive⟩ := hstep
      have reversed := ih p.vertex outgoing nextIncoming «right» hedge hmark hq
      have atJoin : ActiveAt C A p.vertex incoming outgoing := by
        simpa only [hp] using hactive
      exact reversed.append_last (symmetric _ _ _ _ edge)
        ((activeAt_swap C A p.vertex incoming outgoing).mp atJoin)

theorem MarkedRoute.reverse {V : Type u} {G : MarkedGraph V}
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    {C A : V → Prop} {x y : V} {«left» «right» : Mark}
    (h : MarkedRoute G C A x y «left» «right») : MarkedRoute G C A y x «right» «left» := by
  obtain ⟨«first», incoming, rest, edge, hr⟩ := h
  exact reverse_after_first G symmetric C A hr x «left» incoming «right» edge rfl rfl

theorem MarkedRoute.mono {V : Type u} {G : MarkedGraph V}
    {C₁ C₂ A₁ A₂ : V → Prop} (hC : ∀ x, C₂ x → C₁ x) (hA : ∀ x, A₁ x → A₂ x)
    {x y : V} {«left» «right» : Mark} (h : MarkedRoute G C₁ A₁ x y «left» «right») :
    MarkedRoute G C₂ A₂ x y «left» «right» := by
  obtain ⟨«first», incoming, rest, edge, hr⟩ := h
  have mapped := hr.map (fun identityValue => identityValue) (transition_mono G C₁ C₂ A₁ A₂ hC hA)
  exact ⟨«first», incoming, rest, edge, by simpa using mapped⟩

/-- Distinct endpoints exclude the zero route. Every actual transition sets
an incoming mark, so the final endpoint cannot retain the initial `none`. -/
theorem marked_of_distinct_route {V : Type u} (G : MarkedGraph V) (C A : V → Prop)
    (x y : V) (hne : x ≠ y) {last : Option Mark} {xs : List (Arrival V)}
    (h : Route (Transition G C A) ⟨x, none⟩ xs ⟨y, last⟩) :
    ∃ «left» «right», MarkedRoute G C A x y «left» «right» := by
  cases xs with
  | nil =>
      cases h
      exact (hne rfl).elim
  | cons «next» rest =>
      cases h with
      | cons hstep hrest =>
          obtain ⟨«left», incoming, edge, hmark, _⟩ := hstep
          obtain ⟨«right», hright⟩ := ActiveWalkReduction.some_arrival_preserved hrest ⟨incoming, hmark⟩
          have nextEq : «next» = ⟨«next».vertex, some incoming⟩ := Arrival.eq_of_fields rfl hmark
          have endEq : last = some «right» := hright
          exact ⟨«left», «right», «next».vertex, incoming, rest, edge, by
            simpa only [nextEq, endEq] using hrest⟩

theorem inducing_marked_route {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (h : InducingPath D x y) :
    ∃ «left» «right», MarkedRoute (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y)
      (Observed x) (Observed y) «left» «right» := by
  obtain ⟨hne, last, xs, hr, _⟩ := h
  apply marked_of_distinct_route (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y)
    (Observed x) (Observed y) ?_ hr
  intro eq
  exact hne (Sum.inl.inj (Sum.inl.inj eq))

theorem marked_inducing_left_head {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) {«left» «right» : Mark}
    (h : MarkedRoute (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y)
      (Observed x) (Observed y) «left» «right») (flag : ¬ HPLTarget.TailFlag D x y) : «left» = .head := by
  obtain ⟨«first», incoming, rest, edge, hr⟩ := h
  exact first_mark_head_of_not_tail_flag D x y flag Nonlatent (EndpointAncestor D x y)
    (fun _ h => h) «left» incoming edge rfl hr rfl

theorem marked_inducing_right_head {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) {«left» «right» : Mark}
    (h : MarkedRoute (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y)
      (Observed x) (Observed y) «left» «right») (flag : ¬ HPLTarget.TailFlag D y x) : «right» = .head := by
  have reverse := h.reverse (arrow_graph_symm D.arrow)
  have swapped := reverse.mono (fun _ h => h) (endpoint_ancestor_swap D x y)
  exact marked_inducing_left_head D y x swapped flag

end RestrictedCausal.FramedWalk
