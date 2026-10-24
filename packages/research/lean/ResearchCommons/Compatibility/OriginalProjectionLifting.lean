import GeneralActiveWalkReduction

/-! Portable proof-only compatibility: instantiate the original generalized
previous arrival as some incoming. Source/path/activity statements unchanged. -/

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Lift every active projected path to a genuine original-DAG active path.
The converse, including active latent-collider detours, remains explicit.
-/

namespace RestrictedCausal.OriginalProjection

open SelectedWalk CanonicalSelection LatentRoots
open SourceSelection (AncestorOf)

universe u v w

theorem original_arrow_mixed_laws {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : MixedLaws (arrowGraph D.arrow) := by
  constructor
  · exact arrow_graph_symm D.arrow
  · intro a ma mb h
    have haa : D.arrow a a := by
      rcases h with ⟨ha, _⟩ | ⟨ha, _⟩ <;> exact ha
    have hbad := D.acyclic a [a] (.cons haa (.nil a))
    cases hbad
  · intro a b h
    rcases h with ⟨_, _, hbad⟩ | ⟨_, hbad, _⟩ <;> exact Mark.noConfusion hbad

theorem original_retained_activity {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) (a : Sum X S)
    (incoming outgoing : Mark) :
    ActiveAt (retainedCondition C) (AncestorOf (arrowGraph D.arrow) (retainedCondition C))
      (.inl a) incoming outgoing ↔
      ActiveAt C (AncestorOf (projection D) C) a incoming outgoing := by
  by_cases hc : incoming = .head ∧ outgoing = .head
  · simp only [ActiveAt, if_pos hc]
    exact original_retained_condition_ancestry D C a
  · simp only [ActiveAt, if_neg hc]
    exact Iff.rfl

/-- Every original latent interior occurrence is a genuine unconditioned
noncollider. The full route may repeat vertices; the later true-ancestor
loop-reduction theorem, not an assumed simplicity claim, handles that. -/
theorem lift_latent_noncollider {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    (latent : List L) {a b : SourceVertex X S L} {ma mb : Mark} {previous : Option Mark}
    (h : NoncolliderRoute (arrowGraph D.arrow) a ma
      (latent.map (fun l => Sum.inr l : L → SourceVertex X S L)) b mb)
    (hactive : match previous with
      | none => True
      | some m => ActiveAt (retainedCondition C)
          (AncestorOf (arrowGraph D.arrow) (retainedCondition C)) a m ma) :
    ∃ ys, Route (Transition (arrowGraph D.arrow) (retainedCondition C)
      (AncestorOf (arrowGraph D.arrow) (retainedCondition C))) ⟨a, previous⟩ ys ⟨b, some mb⟩ := by
  induction latent generalizing a ma previous with
  | nil =>
      cases h with
      | single hedge => exact ⟨[⟨b, some mb⟩], .cons ⟨ma, mb, hedge, rfl, hactive⟩ (.nil _)⟩
  | cons l ls ih =>
      cases h with
      | @step _ _ _ _ incoming outgoing _ _ hedge hn tail =>
          have hl : ActiveAt (retainedCondition C)
              (AncestorOf (arrowGraph D.arrow) (retainedCondition C)) (.inr l) incoming outgoing := by
            simp [ActiveAt, hn, retainedCondition]
          obtain ⟨ys, hy⟩ := ih (previous := some incoming) tail hl
          exact ⟨⟨.inr l, some incoming⟩ :: ys, .cons ⟨ma, incoming, hedge, rfl, hactive⟩ hy⟩

def originalRetainedState {X : Type u} {S : Type v} {L : Type w}
    (p : Arrival (Sum X S)) : Arrival (SourceVertex X S L) := ⟨.inl p.vertex, p.incoming⟩

theorem lift_projected_step {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {p q : Arrival (Sum X S)} (h : Transition (projection D) C (AncestorOf (projection D) C) p q) :
    ∃ ys, Route (Transition (arrowGraph D.arrow) (retainedCondition C)
      (AncestorOf (arrowGraph D.arrow) (retainedCondition C)))
      (originalRetainedState p) ys (originalRetainedState q) := by
  obtain ⟨outgoing, incoming, ⟨_, latent, hpath⟩, hmark, hactive⟩ := h
  have ha : match p.incoming with
      | none => True
      | some m => ActiveAt (retainedCondition C)
          (AncestorOf (arrowGraph D.arrow) (retainedCondition C)) (.inl p.vertex) m outgoing := by
    cases hpm : p.incoming with
    | none => trivial
    | some m =>
        apply (original_retained_activity D C p.vertex m outgoing).mpr
        simpa only [hpm] using hactive
  obtain ⟨ys, hy⟩ := lift_latent_noncollider D C latent hpath ha
  have hq : (⟨.inl q.vertex, some incoming⟩ : Arrival (SourceVertex X S L)) =
      originalRetainedState q := by
    apply Arrival.eq_of_fields
    · rfl
    · exact hmark.symm
  exact ⟨ys, hq ▸ hy⟩

theorem lift_projected_route {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {p q : Arrival (Sum X S)} {xs : List (Arrival (Sum X S))}
    (h : Route (Transition (projection D) C (AncestorOf (projection D) C)) p xs q) :
    ∃ ys, Route (Transition (arrowGraph D.arrow) (retainedCondition C)
      (AncestorOf (arrowGraph D.arrow) (retainedCondition C)))
      (originalRetainedState p) ys (originalRetainedState q) := by
  induction h with
  | nil p => exact ⟨[], .nil _⟩
  | cons hstep htail ih =>
      obtain ⟨front, hf⟩ := lift_projected_step D C hstep
      obtain ⟨back, hb⟩ := ih
      exact ⟨front ++ back, hf.append hb⟩

/-- One full original d/m-connection implication with original latent vertices
kept in the witness. No uniform arrival-mark assumption is imposed on them. -/
theorem projected_connection_lifts {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) (a b : Sum X S)
    (h : ActiveConnection (projection D) C a b) :
    ActiveConnection (arrowGraph D.arrow) (retainedCondition C) (.inl a) (.inl b) := by
  obtain ⟨lastMark, xs, hp, _⟩ := h
  obtain ⟨ys, hy⟩ := lift_projected_route D C hp
  obtain ⟨r, zs, hz, hvertex, hsimple⟩ := ActiveWalkReduction.active_walk_to_simple
    (arrowGraph D.arrow) (original_arrow_mixed_laws D) (retainedCondition C) hy
  rcases r with ⟨rv, rm⟩
  change rv = .inl b at hvertex
  subst rv
  exact ⟨rm, zs, hz, hsimple⟩

end RestrictedCausal.OriginalProjection
