import ReadyRetainedNormalization

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Complete original-DAG/route-projection active-connection equivalence. The
latent-collider case is discharged by the preceding detour construction.
-/

namespace RestrictedCausal.OriginalProjection

open SelectedWalk CanonicalSelection LatentRoots
open SourceSelection (AncestorOf)

universe u v w

theorem ready_latent_noncollider {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) {l : L} {incoming outgoing : Mark}
    (h : ActiveAt (retainedCondition C) (readyAncestor D C) (.inr l) incoming outgoing) :
    ¬ (incoming = .head ∧ outgoing = .head) := by
  intro hh
  have hbad : False := by simpa [ActiveAt, hh, readyAncestor] using h
  exact hbad

/-- Read the entire initial latent block, preserving both endpoint marks and
an exact suffix-list equation. Its internal noncolliders are derived from the
normalized relation, not hypothesized about the original active path. -/
theorem split_ready_latent_block {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {l : L} {previous : Mark} {xs : List (Arrival (SourceVertex X S L))}
    {b : Sum X S} {lastMark : Option Mark}
    (h : Route (ReadyStep D C) ⟨.inr l, some previous⟩ xs ⟨.inl b, lastMark⟩) :
    ∃ outgoing latent z finalMark rest prefix,
      ¬ (previous = .head ∧ outgoing = .head) ∧
      NoncolliderRoute (arrowGraph D.arrow) (.inr l) outgoing
        (latent.map (fun k => Sum.inr k : L → SourceVertex X S L)) (.inl z) finalMark ∧
      Route (ReadyStep D C) ⟨.inl z, some finalMark⟩ rest ⟨.inl b, lastMark⟩ ∧
      xs = prefix ++ (⟨.inl z, some finalMark⟩ :: rest) := by
  induction xs generalizing l previous with
  | nil => cases h
  | cons next xs ih =>
      cases h with
      | cons hstep htail =>
          rcases next with ⟨nv, nm⟩
          obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
          change nm = some incoming at hmark
          subst nm
          have hn := ready_latent_noncollider D C hactive
          cases nv with
          | inl z => exact ⟨outgoing, [], z, incoming, xs, [], hn, .single hedge, htail, rfl⟩
          | inr k =>
              obtain ⟨nextOut, latent, z, finalMark, rest, prefix, hnc, hp, hr, heq⟩ := ih htail
              exact ⟨outgoing, k :: latent, z, finalMark, rest,
                ⟨.inr k, some incoming⟩ :: prefix, hn, .step hedge hnc hp, hr,
                congrArg (List.cons ⟨.inr k, some incoming⟩) heq⟩

theorem ready_retained_optional_activity {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) (a : Sum X S)
    (previous : Option Mark) (outgoing : Mark)
    (h : match previous with
      | none => True
      | some m => ActiveAt (retainedCondition C) (readyAncestor D C) (.inl a) m outgoing) :
    match previous with
      | none => True
      | some m => ActiveAt C (AncestorOf (projection D) C) a m outgoing := by
  cases previous with
  | none => trivial
  | some m => exact (original_retained_activity D C a m outgoing).mp h

theorem contract_ready_aux {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) (n : Nat) :
    ∀ (a : Sum X S) (previous : Option Mark) (xs : List (Arrival (SourceVertex X S L)))
      (b : Sum X S) (lastMark : Option Mark), xs.length = n →
      Route (ReadyStep D C) ⟨.inl a, previous⟩ xs ⟨.inl b, lastMark⟩ →
      NoObservedRepeat SourceSelection.isSelected (⟨.inl a, previous⟩ :: xs) →
      ∃ ys, Route (Transition (projection D) C (AncestorOf (projection D) C))
        ⟨a, previous⟩ ys ⟨b, lastMark⟩ := by
  refine Nat.strongRecOn n ?_
  intro n ih a previous xs b lastMark hlength h hobs
  cases xs with
  | nil =>
      cases h
      exact ⟨[], .nil _⟩
  | cons next tail =>
      cases h with
      | cons hfirst htail =>
          rcases next with ⟨nv, nm⟩
          obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hfirst
          change nm = some incoming at hmark
          subst nm
          cases nv with
          | inl z =>
              have hne : a ≠ z := by
                intro heq
                exact List.rel_of_pairwise_cons hobs List.mem_cons_self (congrArg Sum.inl heq)
              have hp : (projection D).edge a z outgoing incoming := ⟨hne, [], .single hedge⟩
              have hlt : tail.length < n := by simp only [List.length_cons] at hlength; omega
              obtain ⟨ys, hy⟩ := ih tail.length hlt z (some incoming) tail b lastMark rfl htail
                (List.Pairwise.of_cons hobs)
              exact ⟨⟨z, some incoming⟩ :: ys, .cons
                ⟨outgoing, incoming, hp, rfl,
                  ready_retained_optional_activity D C a previous outgoing hactive⟩ hy⟩
          | inr l =>
              obtain ⟨nextOut, latent, z, finalMark, rest, prefix, hnc, hp, hr, heq⟩ :=
                split_ready_latent_block D C htail
              have hmem : (⟨.inl z, some finalMark⟩ : Arrival (SourceVertex X S L)) ∈ tail := by
                rw [heq]
                exact List.mem_append_right prefix List.mem_cons_self
              have hne : a ≠ z := by
                intro haz
                exact List.rel_of_pairwise_cons hobs (List.mem_cons_of_mem _ hmem)
                  (congrArg Sum.inl haz)
              have hproject : (projection D).edge a z outgoing finalMark :=
                ⟨hne, l :: latent, .step hedge hnc hp⟩
              have hsub : (⟨.inl z, some finalMark⟩ :: rest) <+ tail := by
                rw [heq]
                exact List.sublist_append_right _ _
              have hrestObs := (List.Pairwise.of_cons (List.Pairwise.of_cons hobs)).sublist hsub
              have hlt : rest.length < n := by
                rw [heq] at hlength
                simp only [List.length_cons, List.length_append] at hlength
                omega
              obtain ⟨ys, hy⟩ := ih rest.length hlt z (some finalMark) rest b lastMark rfl hr hrestObs
              exact ⟨⟨z, some finalMark⟩ :: ys, .cons
                ⟨outgoing, finalMark, hproject, rfl,
                  ready_retained_optional_activity D C a previous outgoing hactive⟩ hy⟩

theorem contract_ready_route {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop)
    {a b : Sum X S} {previous lastMark : Option Mark}
    {xs : List (Arrival (SourceVertex X S L))}
    (h : Route (ReadyStep D C) ⟨.inl a, previous⟩ xs ⟨.inl b, lastMark⟩)
    (hobs : NoObservedRepeat SourceSelection.isSelected (⟨.inl a, previous⟩ :: xs)) :
    ∃ ys, Route (Transition (projection D) C (AncestorOf (projection D) C))
      ⟨a, previous⟩ ys ⟨b, lastMark⟩ :=
  contract_ready_aux D C xs.length a previous xs b lastMark rfl h hobs

theorem original_connection_projects {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) (a b : Sum X S)
    (h : ActiveConnection (arrowGraph D.arrow) (retainedCondition C) (.inl a) (.inl b)) :
    ActiveConnection (projection D) C a b := by
  obtain ⟨lastMark, xs, hp, _⟩ := h
  obtain ⟨ready, hready⟩ := resolve_raw_route D C hp
  obtain ⟨r, ys, hy, hvertex, hobs⟩ := ready_retained_simple D C hready
  rcases r with ⟨rv, rm⟩
  change rv = .inl b at hvertex
  subst rv
  obtain ⟨projected, hprojected⟩ := contract_ready_route D C hy hobs
  obtain ⟨last, zs, hz, hlast, hsimple⟩ := ActiveWalkReduction.active_walk_to_simple
    (projection D) (projection_mixed_laws D) C hprojected
  rcases last with ⟨lv, lm⟩
  change lv = b at hlast
  subst lv
  exact ⟨lm, zs, hz, hsimple⟩

/-- Exact original active-path equivalence, including unknown confounders and
conditioned retained selection vertices. Original latent colliders were handled
by actual detours, so no no-latent-collider restriction is present. -/
theorem original_projection_connection_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) (a b : Sum X S) :
    ActiveConnection (arrowGraph D.arrow) (retainedCondition C) (.inl a) (.inl b) ↔
      ActiveConnection (projection D) C a b :=
  ⟨original_connection_projects D C a b, projected_connection_lifts D C a b⟩

end RestrictedCausal.OriginalProjection
