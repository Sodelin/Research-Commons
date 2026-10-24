import OriginalLatentProjection


/- Pinned-context proof variant: expose the SAME identity maps/simplification,
or eliminate the existing impossible Sum equality. All original theorem and
source/graph/conditioning hypotheses and conclusion semantics remain. -/
/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Exact original-DAG/retained-projection ancestry by explicit directed-route
splitting and contraction. General d/m-separation remains separate.
-/

namespace RestrictedCausal.OriginalProjection

open SelectedWalk CanonicalSelection LatentRoots
open SourceSelection (AncestorOf)

universe u v w

theorem directed_noncollider_route {V : Type u} (D : V → V → Prop)
    {a b : V} (mids : List V) (h : Route D a (mids ++ [b]) b) :
    NoncolliderRoute (arrowGraph D) a .tail mids b .head := by
  induction mids generalizing a with
  | nil =>
      cases h with
      | cons hedge htail => exact .single (Or.inl ⟨hedge, rfl, rfl⟩)
  | cons z zs ih =>
      cases h with
      | cons hedge htail =>
          exact .step (Or.inl ⟨hedge, rfl, rfl⟩)
            (fun hbad => Mark.noConfusion hbad.2) (ih htail)

theorem split_latent_prefix {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {l : L} {xs : List (SourceVertex X S L)} {b : Sum X S}
    (h : Route D.arrow (.inr l) xs (.inl b)) :
    ∃ latent : List L, ∃ z rest,
      Route D.arrow (.inr l)
        (latent.map (fun k => Sum.inr k : L → SourceVertex X S L) ++ [.inl z]) (.inl z) ∧
      Route D.arrow (.inl z) rest (.inl b) ∧
      xs = latent.map (fun k => Sum.inr k : L → SourceVertex X S L) ++ (.inl z :: rest) := by
  induction xs generalizing l with
  | nil => cases h
  | cons «next» xs ih =>
      cases h with
      | cons hedge htail =>
          cases «next» with
          | inl z => exact ⟨[], z, xs, .cons hedge (.nil _), htail, rfl⟩
          | inr k =>
              obtain ⟨latent, z, rest, hp, hr, heq⟩ := ih htail
              exact ⟨k :: latent, z, rest, .cons hedge hp, hr,
                congrArg (List.cons (.inr k)) heq⟩

theorem latent_directed_block_projects {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {a b : Sum X S} (latent : List L)
    (h : Route D.arrow (.inl a)
      (latent.map (fun k => Sum.inr k : L → SourceVertex X S L) ++ [.inl b]) (.inl b)) :
    Directed (projection D) a b := by
  have hne : a ≠ b := by
    intro heq
    subst b
    have hempty := D.acyclic (.inl a) _ h
    have hlength := congrArg List.length hempty
    simp only [List.length_append, List.length_map, List.length_singleton, List.length_nil] at hlength
    omega
  exact ⟨hne, latent, directed_noncollider_route D.arrow _ h⟩

theorem contract_directed_aux {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (n : Nat) :
    ∀ (a : Sum X S) (xs : List (SourceVertex X S L)) (b : Sum X S), xs.length = n →
      Route D.arrow (.inl a) xs (.inl b) → ∃ ys, Route (Directed (projection D)) a ys b := by
  refine Nat.strongRecOn n ?_
  intro n ih a xs b hlength h
  cases xs with
  | nil =>
      cases h
      exact ⟨[], .nil _⟩
  | cons «next» tail =>
      cases h with
      | cons hedge htail =>
          cases «next» with
          | inl z =>
              have hp := latent_directed_block_projects D ([] : List L) (.cons hedge (.nil (Sum.inl z : SourceVertex X S L)))
              have hlt : tail.length < n := by simp only [List.length_cons] at hlength; omega
              obtain ⟨ys, hy⟩ := ih tail.length hlt z tail b rfl htail
              exact ⟨z :: ys, .cons hp hy⟩
          | inr l =>
              obtain ⟨latent, z, rest, hp, hr, heq⟩ := split_latent_prefix D htail
              have hblock := latent_directed_block_projects D (l :: latent) (.cons hedge hp)
              have hlt : rest.length < n := by
                rw [heq] at hlength
                simp only [List.length_cons, List.length_append, List.length_map] at hlength
                omega
              obtain ⟨ys, hy⟩ := ih rest.length hlt z rest b rfl hr
              exact ⟨z :: ys, .cons hblock hy⟩

theorem contract_directed_route {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {a b : Sum X S} {xs : List (SourceVertex X S L)}
    (h : Route D.arrow (.inl a) xs (.inl b)) :
    ∃ ys, Route (Directed (projection D)) a ys b :=
  contract_directed_aux D xs.length a xs b rfl h

theorem arrow_directed_exact {V : Type u} (D : V → V → Prop) (a b : V) :
    Directed (arrowGraph D) a b ↔ D a b := by
  change ((D a b ∧ _ ∧ _) ∨ (D b a ∧ _ ∧ _)) ↔ _
  simp

/-- All retained ancestry, including ancestry into the original selection set,
is preserved. The reverse implication is proved by latent-block contraction. -/
theorem retained_reach_exact {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (a b : Sum X S) :
    Reach (arrowGraph D.arrow) (.inl a) (.inl b) ↔ Reach (projection D) a b := by
  constructor
  · rintro ⟨xs, hx⟩
    have hp := hx.map (fun identityValue => identityValue) (fun x y hxy => (arrow_directed_exact D.arrow x y).mp hxy)
    have hp' : Route D.arrow (.inl a) xs (.inl b) := by
      simpa using hp
    exact contract_directed_route D hp'
  · rintro ⟨xs, hx⟩
    obtain ⟨ys, hy, _⟩ := projection_route_lift D hx
    have hp := hy.map (fun identityValue => identityValue) (fun x y hxy => (arrow_directed_exact D.arrow x y).mpr hxy)
    exact ⟨_, hp⟩

def retainedCondition {R : Type u} {L : Type v} (C : R → Prop) : Sum R L → Prop
  | .inl r => C r
  | .inr _ => False

theorem original_retained_condition_ancestry {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (C : Sum X S → Prop) (a : Sum X S) :
    AncestorOf (arrowGraph D.arrow) (retainedCondition C) (.inl a) ↔
      AncestorOf (projection D) C a := by
  constructor
  · rintro ⟨v, hp, hc⟩
    cases v with
    | inl b => exact ⟨b, (retained_reach_exact D a b).mp hp, hc⟩
    | inr l => exact hc.elim
  · rintro ⟨b, hp, hc⟩
    exact ⟨.inl b, (retained_reach_exact D a b).mpr hp, hc⟩

end RestrictedCausal.OriginalProjection
