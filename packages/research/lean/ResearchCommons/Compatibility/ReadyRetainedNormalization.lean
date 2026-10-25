import LatentColliderDetours


/- Pinned-context proof variant: expose the SAME identity maps/simplification,
or eliminate the existing impossible Sum equality. All original theorem and
source/graph/conditioning hypotheses and conclusion semantics remain. -/
/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Erase only retained-vertex return segments, so resolved latent colliders stay
resolved. Latent occurrences may still repeat and are not assumed simple.
-/

namespace RestrictedCausal.OriginalProjection

open SelectedWalk CanonicalSelection LatentRoots
open SourceSelection (AncestorOf)

universe u v w

theorem ready_ancestor_implies_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) {a : SourceVertex X S L}
    (h : readyAncestor D C a) : AncestorOf (arrowGraph D.arrow) (retainedCondition C) a := by
  cases a with
  | inl r => exact h
  | inr l => exact h.elim

theorem ready_step_to_raw {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {p q : Arrival (SourceVertex X S L)} (h : ReadyStep D C p q) :
    Transition (arrowGraph D.arrow) (retainedCondition C)
      (AncestorOf (arrowGraph D.arrow) (retainedCondition C)) p q := by
  obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := h
  refine ⟨outgoing, incoming, hedge, hmark, ?_⟩
  cases hpm : p.incoming with
  | none => trivial
  | some previous =>
      have ha : ActiveAt (retainedCondition C) (readyAncestor D C) p.vertex previous outgoing := by
        simpa only [hpm] using hactive
      by_cases hh : previous = .head ∧ outgoing = .head
      · simp only [ActiveAt, if_pos hh] at ha ⊢
        exact ready_ancestor_implies_ancestor D C ha
      · simpa only [ActiveAt, if_neg hh] using ha

theorem ready_route_to_raw {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {p q : Arrival (SourceVertex X S L)} {xs : List (Arrival (SourceVertex X S L))}
    (h : Route (ReadyStep D C) p xs q) :
    Route (Transition (arrowGraph D.arrow) (retainedCondition C)
      (AncestorOf (arrowGraph D.arrow) (retainedCondition C))) p xs q := by
  have hp := h.map (fun identityValue => identityValue) (fun _ _ hstep => ready_step_to_raw D C hstep)
  simpa using hp

theorem raw_retained_step_is_ready {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {p q : Arrival (SourceVertex X S L)} {a : Sum X S} (hp : p.vertex = .inl a)
    (h : Transition (arrowGraph D.arrow) (retainedCondition C)
      (AncestorOf (arrowGraph D.arrow) (retainedCondition C)) p q) : ReadyStep D C p q := by
  rcases p with ⟨pv, pm⟩
  change pv = .inl a at hp
  subst pv
  exact h

theorem ready_splice_retained {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {p q r : Arrival (SourceVertex X S L)} {loop : List (Arrival (SourceVertex X S L))}
    {a : Sum X S} (hp : p.vertex = .inl a)
    (hloop : Route (ReadyStep D C) p loop q) (hv : p.vertex = q.vertex)
    (hnext : ReadyStep D C q r) : ReadyStep D C p r :=
  raw_retained_step_is_ready D C hp
    (ActiveWalkReduction.splice_departure (arrowGraph D.arrow) (original_arrow_mixed_laws D)
      (retainedCondition C) (ready_route_to_raw D C hloop) hv (ready_step_to_raw D C hnext))

theorem observedValue_some_vertex {R : Type u} {L : Type v}
    {p : Arrival (Sum R L)} {a : R} (h : SourceSelection.observedValue p = some a) :
    p.vertex = .inl a := by
  rcases p with ⟨pv, pm⟩
  cases pv with
  | inl r =>
      have heq : r = a := Option.some.inj h
      subst r
      rfl
  | inr l => cases h

/-- Every repeated RETAINED vertex is removed by a valid retained splice.
Latent departures are unchanged, so no latent collider is reintroduced. -/
theorem ready_retained_simple {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {p q : Arrival (SourceVertex X S L)} {xs : List (Arrival (SourceVertex X S L))}
    (h : Route (ReadyStep D C) p xs q) :
    ∃ r ys, Route (ReadyStep D C) p ys r ∧ r.vertex = q.vertex ∧
      NoObservedRepeat SourceSelection.isSelected (p :: ys) := by
  classical
  induction h with
  | nil p => exact ⟨p, [], .nil p, rfl, .cons (by intro r hr; cases hr) .nil⟩
  | @cons p q r xs hpq hqr ih =>
      obtain ⟨last, ys, hy, hlast, hobs⟩ := ih
      rcases p with ⟨pv, pm⟩
      cases pv with
      | inr l =>
          exact ⟨last, q :: ys, .cons hpq hy, hlast,
            .cons (fun _ _ _ => trivial) hobs⟩
      | inl a =>
          have htrace := (SourceSelection.noObservedRepeat_iff_trace_nodup _).mp hobs
          by_cases hmem : a ∈ (q :: ys).filterMap SourceSelection.observedValue
          · obtain ⟨«at», hat, hatValue⟩ := List.mem_filterMap.mp hmem
            have hatVertex := observedValue_some_vertex hatValue
            obtain ⟨«prefix», hprefix⟩ := hy.prefix_of_mem hat
            obtain ⟨suffix, hsuffix, hsub⟩ := hy.suffix_of_mem hat
            have hloop := Route.cons hpq hprefix
            have hshort := hobs.sublist hsub
            cases hsuffix with
            | nil =>
                exact ⟨⟨.inl a, pm⟩, [], .nil _, hatVertex.symm.trans hlast,
                  .cons (by intro z hz; cases hz) .nil⟩
            | @cons «at» «next» last tail hstep htail =>
                refine ⟨last, «next» :: tail, .cons ?_ htail, hlast, ?_⟩
                · exact ready_splice_retained D C rfl hloop hatVertex.symm hstep
                · apply (SourceSelection.noObservedRepeat_iff_trace_nodup _).mpr
                  change (a :: («next» :: tail).filterMap SourceSelection.observedValue).Nodup
                  have hn := (SourceSelection.noObservedRepeat_iff_trace_nodup _).mp hshort
                  simpa only [List.filterMap_cons, hatValue] using hn
          · refine ⟨last, q :: ys, .cons hpq hy, hlast, ?_⟩
            apply (SourceSelection.noObservedRepeat_iff_trace_nodup _).mpr
            change (a :: (q :: ys).filterMap SourceSelection.observedValue).Nodup
            exact List.Nodup.cons hmem htrace

end RestrictedCausal.OriginalProjection
