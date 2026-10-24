import MAGPathLifting

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Maximality follows from the already proved one-way representation, because
each missing inducing edge has an actual observed source separator, and any
source separator also separates in the MAG. This does not infer the still
unproved converse representation direction from maximality.
-/

namespace RestrictedCausal.HPLTarget

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation DiscriminatingStatus MAGLifting

universe u v w

theorem endpoint_mark_exists {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : ∃ m, EndpointMark D x y m := by
  classical
  by_cases h : TailFlag D x y
  · exact ⟨.tail, Or.inl ⟨rfl, h⟩⟩
  · exact ⟨.head, Or.inr ⟨rfl, h⟩⟩

theorem mag_adjacent_iff_inducing {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : Adjacent (mag D) x y ↔ InducingPath D x y := by
  constructor
  · rintro ⟨mx, my, hedge⟩
    exact hedge.1
  · intro h
    obtain ⟨mx, hx⟩ := endpoint_mark_exists D x y
    obtain ⟨my, hy⟩ := endpoint_mark_exists D y x
    exact ⟨mx, my, h, hx, hy⟩

theorem source_separator_is_mag_separator {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) (hx : ¬ Z x) (hy : ¬ Z y)
    (hsep : ¬ ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y)) :
    ¬ ActiveConnection (mag D) Z x y :=
  fun h => hsep (mag_connection_implies_original D Z x y hx hy h)

def Maximal {V : Type u} (G : MarkedGraph V) : Prop :=
  ∀ x y, x ≠ y → ¬ Adjacent G x y → ∃ Z : V → Prop,
    ¬ Z x ∧ ¬ Z y ∧ ¬ ActiveConnection G Z x y

theorem mag_maximal {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : Maximal (mag D) := by
  classical
  intro x y hxy missing
  have notInducing : ¬ InducingPath D x y := fun h => missing ((mag_adjacent_iff_inducing D x y).mpr h)
  have existsSourceSeparator : ∃ Z : X → Prop, ¬ Z x ∧ ¬ Z y ∧
      ¬ ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y) := by
    by_contra noSeparator
    apply notInducing
    apply (inducing_iff_inseparable D x y).mpr
    refine ⟨hxy, ?_⟩
    intro Z hx hy
    by_contra separated
    exact noSeparator ⟨Z, hx, hy, separated⟩
  obtain ⟨Z, hx, hy, hsep⟩ := existsSourceSeparator
  exact ⟨Z, hx, hy, source_separator_is_mag_separator D Z x y hx hy hsep⟩

/-- Both graph-class obligations are proved for the literal target, with no
bounded hidden-source substitution. Exact full separation representation is
not a field of this validity package and remains a separate dependency. -/
theorem literal_mag_valid {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : AncestralLaws (mag D) ∧ SingleEdges (mag D) ∧ Maximal (mag D) :=
  ⟨mag_ancestral_laws D, mag_single_edges D, mag_maximal D⟩

end RestrictedCausal.HPLTarget
