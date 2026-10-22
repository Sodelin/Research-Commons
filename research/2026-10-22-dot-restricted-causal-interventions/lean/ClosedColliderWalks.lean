import ObservedMAGAncestry

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Physical loop erasure with a backward-closed collider-activation set. Unlike
the earlier true-ancestor theorem, the noncollider exclusion set and the
collider ancestor set need not be derived from the same conditioning set.
This is needed for actual inducing-walk contraction, not an assumed adapter.
-/

namespace RestrictedCausal.ClosedColliderWalks

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open ActiveWalkReduction SourceSelection (AncestorOf)

universe u v w

def BackwardClosed {V : Type u} (G : MarkedGraph V) (A : V → Prop) : Prop :=
  ∀ x y, Directed G x y → A y → A x

theorem ancestor_backward_closed {V : Type u} (G : MarkedGraph V) (C : V → Prop) :
    BackwardClosed G (AncestorOf G C) := by
  intro x y edge h
  obtain ⟨z, ⟨zs, path⟩, hz⟩ := h
  exact ⟨z, ⟨y :: zs, .cons edge path⟩, hz⟩

theorem head_outside_step {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C A : V → Prop) (closed : BackwardClosed G A) {p q : Arrival V}
    (hp : p.incoming = some .head) (hn : ¬ A p.vertex) (h : Transition G C A p q) :
    q.incoming = some .head ∧ ¬ A q.vertex := by
  obtain ⟨outgoing, incoming, edge, mark, active⟩ := h
  have atP : ActiveAt C A p.vertex .head outgoing := by simpa only [hp] using active
  have outTail : outgoing = .tail := by
    cases outgoing with
    | tail => rfl
    | head => exact (hn (by simpa [ActiveAt] using atP)).elim
  subst outgoing
  have inHead : incoming = .head := by
    cases incoming with
    | head => rfl
    | tail => exact (laws.no_tail_tail p.vertex q.vertex edge).elim
  subst incoming
  exact ⟨mark, fun hq => hn (closed _ _ edge hq)⟩

theorem head_outside_route {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C A : V → Prop) (closed : BackwardClosed G A)
    {p q : Arrival V} {xs : List (Arrival V)} (h : Route (Transition G C A) p xs q) :
    p.incoming = some .head → ¬ A p.vertex → q.incoming = some .head ∧ ¬ A q.vertex := by
  induction h with
  | nil p => exact fun hp hn => ⟨hp, hn⟩
  | cons step tail ih =>
      intro hp hn
      obtain ⟨hq, hqn⟩ := head_outside_step G laws C A closed hp hn step
      exact ih hq hqn

theorem closed_splice_departure {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C A : V → Prop) (closed : BackwardClosed G A)
    {p q r : Arrival V} {loop : List (Arrival V)}
    (hloop : Route (Transition G C A) p loop q) (hv : p.vertex = q.vertex)
    (hnext : Transition G C A q r) : Transition G C A p r := by
  cases hloop with
  | nil => exact hnext
  | @cons p first q rest hfirst hrest =>
      have whole : Route (Transition G C A) p (first :: rest) q := .cons hfirst hrest
      obtain ⟨outgoing, incoming, edge, mark, active⟩ := hnext
      refine ⟨outgoing, incoming, ?_, mark, ?_⟩
      · rw [hv]
        exact edge
      · cases hpm : p.incoming with
        | none => trivial
        | some previous =>
            by_cases collider : previous = .head ∧ outgoing = .head
            · simp only [ActiveAt, if_pos collider]
              by_cases activated : A p.vertex
              · exact activated
              · have hpHead := hpm.trans (congrArg some collider.1)
                obtain ⟨hqHead, hqOutside⟩ := head_outside_route G laws C A closed whole hpHead activated
                have hqActive : A q.vertex := by simpa [hqHead, collider.2, ActiveAt] using active
                exact (hqOutside hqActive).elim
            · simp only [ActiveAt, if_neg collider]
              intro conditioned
              obtain ⟨firstOut, firstIn, _, firstMark, firstActive⟩ := hfirst
              have hpActive : ActiveAt C A p.vertex previous firstOut := by
                simpa only [hpm] using firstActive
              have hpHead := (conditioned_active_heads conditioned hpActive).1
              obtain ⟨lastIn, lastMark⟩ := some_arrival_preserved hrest ⟨firstIn, firstMark⟩
              have hqActive : ActiveAt C A q.vertex lastIn outgoing := by
                simpa only [lastMark] using active
              have outHead := (conditioned_active_heads (hv ▸ conditioned) hqActive).2
              exact collider ⟨hpHead, outHead⟩

theorem closed_walk_to_simple {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C A : V → Prop) (closed : BackwardClosed G A)
    {p q : Arrival V} {xs : List (Arrival V)} (h : Route (Transition G C A) p xs q) :
    ∃ r ys, Route (Transition G C A) p ys r ∧ r.vertex = q.vertex ∧
      ((p :: ys).map Arrival.vertex).Nodup := by
  classical
  induction h with
  | nil p => exact ⟨p, [], .nil p, rfl, List.nodup_singleton p.vertex⟩
  | @cons p q r xs step tail ih =>
      obtain ⟨last, ys, route, lastVertex, nodup⟩ := ih
      by_cases occurs : p.vertex ∈ (q :: ys).map Arrival.vertex
      · obtain ⟨at, atMem, sameVertex⟩ := List.mem_map.mp occurs
        obtain ⟨prefix, prefixRoute⟩ := route.prefix_of_mem atMem
        obtain ⟨suffix, suffixRoute, sublist⟩ := route.suffix_of_mem atMem
        have loop := Route.cons step prefixRoute
        have short := nodup.sublist (List.Sublist.map Arrival.vertex sublist)
        cases suffixRoute with
        | nil => exact ⟨p, [], .nil p, sameVertex.symm.trans lastVertex, List.nodup_singleton p.vertex⟩
        | @cons at next last rest nextStep restRoute =>
            refine ⟨last, next :: rest, .cons ?_ restRoute, lastVertex, ?_⟩
            · exact closed_splice_departure G laws C A closed loop sameVertex.symm nextStep
            · simpa only [List.map_cons, sameVertex] using short
      · exact ⟨last, q :: ys, .cons step route, lastVertex, List.Nodup.cons occurs nodup⟩

/-- Loopy marked inducing walks yield actual physically simple inducing paths.
This is used only on the original DAG, which has no tail-tail edges. It is not
an invalid application of the mixed-law reduction to a selected MAG. -/
theorem marked_inducing_walk_is_path {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {left right : Mark} (hne : x ≠ y)
    (h : FramedWalk.MarkedRoute (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y)
      (Observed x) (Observed y) left right) : InducingPath D x y := by
  obtain ⟨xs, route⟩ := h.to_route
  obtain ⟨r, ys, simple, endpoint, nodup⟩ := closed_walk_to_simple
    (arrowGraph D.arrow) (original_arrow_mixed_laws D) Nonlatent (EndpointAncestor D x y)
    (ancestor_backward_closed (arrowGraph D.arrow) (EndpointSelection x y)) route
  have eq : r = ⟨Observed y, r.incoming⟩ := Arrival.eq_of_fields endpoint rfl
  rw [eq] at simple
  exact ⟨hne, r.incoming, ys, simple, nodup⟩

end RestrictedCausal.ClosedColliderWalks
