import OriginalProjectionLifting

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Resolve active original latent colliders by explicit conditioned-descendant
detours. No faithfulness or bound on original latent vertices is assumed here.
-/

namespace RestrictedCausal.OriginalProjection

open SelectedWalk CanonicalSelection LatentRoots
open SourceSelection (AncestorOf)

universe u v w

inductive SafeToCondition {V : Type u} (D : V → V → Prop) (C : V → Prop) : V → V → Prop
  | single {a b} (edge : D a b) (start : ¬ C a) (finish : C b) : SafeToCondition D C a b
  | cons {a b c} (edge : D a b) (start : ¬ C a) (tail : SafeToCondition D C b c) :
      SafeToCondition D C a c

theorem SafeToCondition.start {V : Type u} {D : V → V → Prop} {C : V → Prop}
    {a b : V} (h : SafeToCondition D C a b) : ¬ C a := by
  cases h with
  | single _ hs _ => exact hs
  | cons _ hs _ => exact hs

theorem safe_conditioned_prefix {V : Type u} (D : V → V → Prop) (C : V → Prop)
    {a b : V} {xs : List V} (h : Route D a xs b) :
    ¬ C a → C b → ∃ z, SafeToCondition D C a z := by
  classical
  induction h with
  | nil a => exact fun hn hc => (hn hc).elim
  | @cons a b c xs hab hbc ih =>
      intro ha hc
      by_cases hb : C b
      · exact ⟨b, .single hab ha hb⟩
      · obtain ⟨z, hz⟩ := ih hb hc
        exact ⟨z, .cons hab ha hz⟩

/-- Retained colliders retain their true ancestor activity. Latent colliders
are forbidden in this normalization relation, but are resolved below rather
than assumed absent in the original source. -/
def readyAncestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) : SourceVertex X S L → Prop
  | .inl a => AncestorOf (arrowGraph D.arrow) (retainedCondition C) (.inl a)
  | .inr _ => False

abbrev ReadyStep {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) :=
  Transition (arrowGraph D.arrow) (retainedCondition C) (readyAncestor D C)

theorem conditioned_ready_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) {a : SourceVertex X S L}
    (ha : retainedCondition C a) : readyAncestor D C a := by
  cases a with
  | inl r => exact ⟨.inl r, ⟨[], .nil _⟩, ha⟩
  | inr l => exact ha.elim

/-- Follow a directed path to its first conditioned vertex and return. Only
the turnaround vertex is a collider, and it is retained and conditioned. -/
theorem safe_ready_detour {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {a b : SourceVertex X S L} (h : SafeToCondition D.arrow (retainedCondition C) a b) :
    ∃ ys, Route (ReadyStep D C) ⟨a, some .head⟩ ys ⟨a, some .tail⟩ := by
  induction h with
  | @single a b hab ha hb =>
      refine ⟨[⟨b, some .head⟩, ⟨a, some .tail⟩], .cons ?_ (.cons ?_ (.nil _))⟩
      · refine ⟨.tail, .head, Or.inl ⟨hab, rfl, rfl⟩, rfl, ?_⟩
        simpa [ActiveAt] using ha
      · refine ⟨.head, .tail, Or.inr ⟨hab, rfl, rfl⟩, rfl, ?_⟩
        simpa [ActiveAt] using conditioned_ready_ancestor D C hb
  | @cons a b c hab ha hbc ih =>
      obtain ⟨ys, hy⟩ := ih
      have hfirst : ReadyStep D C ⟨a, some .head⟩ ⟨b, some .head⟩ := by
        refine ⟨.tail, .head, Or.inl ⟨hab, rfl, rfl⟩, rfl, ?_⟩
        simpa [ActiveAt] using ha
      have hback : ReadyStep D C ⟨b, some .tail⟩ ⟨a, some .tail⟩ := by
        refine ⟨.head, .tail, Or.inr ⟨hab, rfl, rfl⟩, rfl, ?_⟩
        simpa [ActiveAt] using hbc.start
      exact ⟨_, (Route.cons hfirst hy).append (.cons hback (.nil _))⟩

theorem latent_collider_detour {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) (l : L)
    (h : AncestorOf (arrowGraph D.arrow) (retainedCondition C) (.inr l)) :
    ∃ ys, Route (ReadyStep D C) ⟨.inr l, some .head⟩ ys ⟨.inr l, some .tail⟩ := by
  obtain ⟨b, ⟨xs, hp⟩, hb⟩ := h
  have hp' := hp.map id (fun a b hab => (arrow_directed_exact D.arrow a b).mp hab)
  obtain ⟨z, hz⟩ := safe_conditioned_prefix D.arrow (retainedCondition C) hp'
    (fun hfalse => hfalse) hb
  exact safe_ready_detour D C hz

theorem resolve_raw_step {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {p q : Arrival (SourceVertex X S L)}
    (h : Transition (arrowGraph D.arrow) (retainedCondition C)
      (AncestorOf (arrowGraph D.arrow) (retainedCondition C)) p q) :
    ∃ ys, Route (ReadyStep D C) p ys q := by
  obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := h
  rcases p with ⟨pv, pm⟩
  cases pv with
  | inl a => exact ⟨[q], .cons ⟨outgoing, incoming, hedge, hmark, hactive⟩ (.nil q)⟩
  | inr l =>
      cases pm with
      | none => exact ⟨[q], .cons ⟨outgoing, incoming, hedge, hmark, trivial⟩ (.nil q)⟩
      | some previous =>
          by_cases hh : previous = .head ∧ outgoing = .head
          · obtain ⟨rfl, rfl⟩ := hh
            have ha : AncestorOf (arrowGraph D.arrow) (retainedCondition C) (.inr l) := by
              simpa [ActiveAt] using hactive
            obtain ⟨ys, hy⟩ := latent_collider_detour D C l ha
            have hlast : ReadyStep D C ⟨.inr l, some .tail⟩ q := by
              refine ⟨.head, incoming, hedge, hmark, ?_⟩
              simp [ActiveAt, retainedCondition]
            exact ⟨_, hy.append (.cons hlast (.nil q))⟩
          · refine ⟨[q], .cons ⟨outgoing, incoming, hedge, hmark, ?_⟩ (.nil q)⟩
            simp [ActiveAt, hh, retainedCondition]

theorem resolve_raw_route {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {p q : Arrival (SourceVertex X S L)} {xs : List (Arrival (SourceVertex X S L))}
    (h : Route (Transition (arrowGraph D.arrow) (retainedCondition C)
      (AncestorOf (arrowGraph D.arrow) (retainedCondition C))) p xs q) :
    ∃ ys, Route (ReadyStep D C) p ys q := by
  induction h with
  | nil p => exact ⟨[], .nil p⟩
  | cons hstep htail ih =>
      obtain ⟨front, hf⟩ := resolve_raw_step D C hstep
      obtain ⟨back, hb⟩ := ih
      exact ⟨front ++ back, hf.append hb⟩

end RestrictedCausal.OriginalProjection
