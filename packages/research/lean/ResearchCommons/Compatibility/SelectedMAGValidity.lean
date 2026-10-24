import LiteralSelectedMAG


/- Pinned-context proof variant: expose the SAME identity maps/simplification,
or eliminate the existing impossible Sum equality. All original theorem and
source/graph/conditioning hypotheses and conclusion semantics remain. -/
/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Ancestral-graph validity of the literal selected MAG endpoint construction.
This does not yet prove its complete m-separation representation or the
shared-separator MAG-MEC theorem. Classical attribution: Richardson--Spirtes;
the target definition follows Hou--Park--Li.
-/

namespace RestrictedCausal.InducingSeparation

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open SourceSelection (AncestorOf)

universe u v w

theorem activeAt_swap {V : Type u} (C A : V → Prop) (x : V) (m n : Mark) :
    ActiveAt C A x m n ↔ ActiveAt C A x n m := by
  cases m <;> cases n <;> exact Iff.rfl

/-- Reversal carries the exact departure condition needed to append the
previous edge. The endpoint's incoming mark is not naively reused. -/
theorem reverse_activity_route {V : Type u} (G : MarkedGraph V)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (C A : V → Prop) {p q : Arrival V} {xs : List (Arrival V)}
    (h : SelectedWalk.Route (Transition G C A) p xs q) :
    ∃ last ys, SelectedWalk.Route (Transition G C A) ⟨q.vertex, none⟩ ys ⟨p.vertex, last⟩ ∧
      (match p.incoming with
      | none => True
      | some previous => DepartureAllowed C A p.vertex last previous) := by
  induction h with
  | nil p =>
      refine ⟨none, [], .nil _, ?_⟩
      cases p.incoming <;> trivial
  | @cons p «next» q rest hstep hrest ih =>
      obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
      obtain ⟨last, ys, hy, hready⟩ := ih
      have backward : Transition G C A ⟨«next».vertex, last⟩ ⟨p.vertex, some outgoing⟩ := by
        refine ⟨incoming, outgoing, symmetric _ _ _ _ hedge, rfl, ?_⟩
        simpa only [hmark, DepartureAllowed] using hready
      refine ⟨some outgoing, ys ++ [⟨p.vertex, some outgoing⟩],
        hy.append (.cons backward (.nil _)), ?_⟩
      cases hm : p.incoming with
      | none => trivial
      | some previous =>
          have ha : ActiveAt C A p.vertex previous outgoing := by
            simpa only [hm] using hactive
          exact (activeAt_swap C A p.vertex previous outgoing).mp ha

theorem active_connection_symm {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C : V → Prop) {x y : V} (h : ActiveConnection G C x y) : ActiveConnection G C y x := by
  obtain ⟨last, xs, hp, _⟩ := h
  obtain ⟨revLast, ys, hy, _⟩ := reverse_activity_route G laws.symmetric C (AncestorOf G C) hp
  obtain ⟨r, zs, hz, hvertex, hnd⟩ := ActiveWalkReduction.active_walk_to_simple G laws C hy
  have heq : r = ⟨x, r.incoming⟩ := Arrival.eq_of_fields hvertex rfl
  rw [heq] at hz
  exact ⟨r.incoming, zs, hz, hnd⟩

theorem inducing_symm {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} (h : InducingPath D x y) : InducingPath D y x := by
  obtain ⟨hne, hp⟩ := (inducing_iff_inseparable D x y).mp h
  apply (inducing_iff_inseparable D y x).mpr
  exact ⟨hne.symm, fun Z hy hx => active_connection_symm (arrowGraph D.arrow)
    (original_arrow_mixed_laws D) (SelectedCondition Z) (hp Z hx hy)⟩

theorem source_directed_acyclic {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : DirectedAcyclic (arrowGraph D.arrow) := by
  intro a xs hp
  have hraw := hp.map (fun identityValue => identityValue) (fun a b hab => (arrow_directed_exact D.arrow a b).mp hab)
  have hnil := D.acyclic a (xs.map (fun identityValue => identityValue)) hraw
  simpa using hnil

theorem reach_antisymm_of_acyclic {V : Type u} (G : MarkedGraph V)
    (hacyclic : DirectedAcyclic G) {a b : V} (hab : Reach G a b) (hba : Reach G b a) : a = b := by
  obtain ⟨xs, hx⟩ := hab
  obtain ⟨ys, hy⟩ := hba
  have hnil := hacyclic a (xs ++ ys) (hx.append hy)
  cases xs with
  | nil => cases hx; rfl
  | cons z zs => cases hnil

end RestrictedCausal.InducingSeparation

namespace RestrictedCausal.HPLTarget

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation

universe u v w

theorem endpoint_tail_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : EndpointMark D x y .tail ↔ TailFlag D x y := by
  simp [EndpointMark]

theorem endpoint_head_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : EndpointMark D x y .head ↔ ¬ TailFlag D x y := by
  simp [EndpointMark]

theorem mag_symmetric {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (mx my : Mark) (h : (mag D).edge x y mx my) :
    (mag D).edge y x my mx := ⟨inducing_symm D h.1, h.2.2, h.2.1⟩

theorem selection_ancestor_predecessor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X}
    (hxy : Reach (arrowGraph D.arrow) (Observed x) (Observed y))
    (hy : SelectionAncestor D y) : SelectionAncestor D x := by
  obtain ⟨s, hs⟩ := hy
  exact ⟨s, reach_trans hxy hs⟩

theorem head_not_source_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {m : Mark} (h : (mag D).edge x y .head m) :
    ¬ Reach (arrowGraph D.arrow) (Observed x) (Observed y) ∧ ¬ SelectionAncestor D x := by
  have hn := (endpoint_head_iff D x y).mp h.2.1
  exact ⟨fun ha => hn (Or.inl ha), fun hs => hn (Or.inr hs)⟩

theorem directed_target_not_selection_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} (h : Directed (mag D) x y) : ¬ SelectionAncestor D y :=
  (head_not_source_ancestor D (mag_symmetric D x y .tail .head h)).2

theorem directed_source_reach {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} (h : Directed (mag D) x y)
    (hn : ¬ SelectionAncestor D x) : Reach (arrowGraph D.arrow) (Observed x) (Observed y) := by
  rcases (endpoint_tail_iff D x y).mp h.2.1 with ha | hs
  · exact ha
  · exact (hn hs).elim

theorem mag_directed_route_lifts {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {xs : List X}
    (h : SelectedWalk.Route (Directed (mag D)) x xs y)
    (hn : ¬ SelectionAncestor D x) :
    Reach (arrowGraph D.arrow) (Observed x) (Observed y) := by
  revert hn
  induction h with
  | nil x => intro _; exact ⟨[], .nil _⟩
  | cons hedge htail ih =>
      intro hn
      exact reach_trans (directed_source_reach D hedge hn)
        (ih (directed_target_not_selection_ancestor D hedge))

theorem mag_directed_end_not_selection {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {xs : List X}
    (h : SelectedWalk.Route (Directed (mag D)) x xs y) :
    ¬ SelectionAncestor D x → ¬ SelectionAncestor D y := by
  induction h with
  | nil x => exact id
  | cons hedge htail ih =>
      intro _
      exact ih (directed_target_not_selection_ancestor D hedge)

theorem mag_no_directed_cycle {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : DirectedAcyclic (mag D) := by
  intro x xs hp
  cases hp with
  | nil => rfl
  | cons hedge htail =>
      have hnext := directed_target_not_selection_ancestor D hedge
      have hx := mag_directed_end_not_selection D htail hnext
      have hforward := directed_source_reach D hedge hx
      have hback := mag_directed_route_lifts D htail hnext
      have heq := reach_antisymm_of_acyclic (arrowGraph D.arrow) (source_directed_acyclic D)
        hforward hback
      exact (hedge.1.1 (Sum.inl.inj (Sum.inl.inj heq))).elim

theorem head_not_mag_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} {m : Mark} (h : (mag D).edge x y .head m) :
    ¬ Reach (mag D) x y := by
  obtain ⟨hnot, hsel⟩ := head_not_source_ancestor D h
  rintro ⟨xs, hp⟩
  exact hnot (mag_directed_route_lifts D hp hsel)

/-- Both endpoints of an undirected MAG edge must be ancestors of selection.
Mutual ordinary ancestry is ruled out by the original DAG, not by assuming
the projected graph ancestral in advance. -/
theorem undirected_endpoints_selected_ancestry {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y : X} (h : (mag D).edge x y .tail .tail) :
    SelectionAncestor D x ∧ SelectionAncestor D y := by
  have hx := (endpoint_tail_iff D x y).mp h.2.1
  have hy := (endpoint_tail_iff D y x).mp h.2.2
  rcases hx with hxy | hxs <;> rcases hy with hyx | hys
  · have heq := reach_antisymm_of_acyclic (arrowGraph D.arrow) (source_directed_acyclic D) hxy hyx
    exact (h.1.1 (Sum.inl.inj (Sum.inl.inj heq))).elim
  · exact ⟨selection_ancestor_predecessor D hxy hys, hys⟩
  · exact ⟨hxs, selection_ancestor_predecessor D hyx hxs⟩
  · exact ⟨hxs, hys⟩

theorem undirected_endpoint_no_heads {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {x y z : X} {m : Mark}
    (hxy : (mag D).edge x y .tail .tail) : ¬ (mag D).edge x z .head m := by
  intro hxz
  exact (head_not_source_ancestor D hxz).2 (undirected_endpoints_selected_ancestry D hxy).1

/-- Standard ancestral-graph axioms, with explicit marked edges. Maximality
and complete m-separation representation are deliberately not fields supplied
without proof; they are later obligations. -/
structure AncestralLaws {V : Type u} (G : MarkedGraph V) : Prop where
  symmetric : ∀ x y mx my, G.edge x y mx my → G.edge y x my mx
  irreflexive : ∀ x mx my, ¬ G.edge x x mx my
  acyclic : DirectedAcyclic G
  head_not_ancestor : ∀ x y m, G.edge x y .head m → ¬ Reach G x y
  undirected_no_heads : ∀ x y z m, G.edge x y .tail .tail → ¬ G.edge x z .head m

theorem mag_ancestral_laws {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : AncestralLaws (mag D) where
  symmetric := mag_symmetric D
  irreflexive := mag_no_self_edge D
  acyclic := mag_no_directed_cycle D
  head_not_ancestor := fun _ _ _ h => head_not_mag_ancestor D h
  undirected_no_heads := fun _ _ _ _ h => undirected_endpoint_no_heads D h

end RestrictedCausal.HPLTarget
