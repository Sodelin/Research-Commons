import RestrictedQueryActions

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

One orientation per unordered observed pair suffices. Reversing endpoints
also transports the actual untargeted-subset index and conditioning set;
it does not silently double the query count or compare different queries.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation

universe u v w v' w'

def reversePairBits {X : Type u} (T : X → Prop) (x y : X)
    (W : UntargetedOutsidePair T x y → Bool) : UntargetedOutsidePair T y x → Bool :=
  fun z => W ⟨z.val, z.property.1, z.property.2.2, z.property.2.1⟩

theorem pair_condition_reverse {X : Type u} (T : X → Prop) (A : X → X → Prop)
    (x y : X) (W : UntargetedOutsidePair T x y → Bool) :
    PairCondition T A x y W = PairCondition T A y x (reversePairBits T x y W) := by
  funext z
  apply propext
  constructor
  · rintro ⟨notX, notY, source⟩
    refine ⟨notY, notX, ?_⟩
    rcases source with ⟨targeted, mask⟩ | ⟨w, label, selected⟩
    · exact Or.inl ⟨targeted, mask.symm⟩
    · exact Or.inr ⟨⟨w.val, w.property.1, w.property.2.2, w.property.2.1⟩, label, selected⟩
  · rintro ⟨notY, notX, source⟩
    refine ⟨notX, notY, ?_⟩
    rcases source with ⟨targeted, mask⟩ | ⟨w, label, selected⟩
    · exact Or.inl ⟨targeted, mask.symm⟩
    · exact Or.inr ⟨⟨w.val, w.property.1, w.property.2.2, w.property.2.1⟩, label, selected⟩

theorem selected_connection_swap {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) :
    ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y) ↔
      ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed y) (Observed x) :=
  ⟨active_connection_symm (arrowGraph D.arrow) (original_arrow_mixed_laws D) (SelectedCondition Z),
    active_connection_symm (arrowGraph D.arrow) (original_arrow_mixed_laws D) (SelectedCondition Z)⟩

theorem ordered_observed_agreement {X : Type u} [LinearOrder X]
    {S : Type v} {L : Type w} {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (E : SourceDAG X S' L')
    (T : X → Prop) (A : X → X → Prop)
    (ordered : ∀ x y, x < y → ∀ W : UntargetedOutsidePair T x y → Bool,
      ActiveConnection (arrowGraph D.arrow) (SelectedCondition (PairCondition T A x y W))
          (Observed x) (Observed y) ↔
        ActiveConnection (arrowGraph E.arrow) (SelectedCondition (PairCondition T A x y W))
          (Observed x) (Observed y)) : ObservedFamilyAgreement D E T A := by
  intro x y distinct W
  rcases lt_or_gt_of_ne distinct with forward | backward
  · exact ordered x y forward W
  · have agreement := ordered y x backward (reversePairBits T x y W)
    rw [← pair_condition_reverse T A x y W] at agreement
    exact (selected_connection_swap D (PairCondition T A x y W) x y).trans
      (agreement.trans (selected_connection_swap E (PairCondition T A x y W) y x))

end RestrictedCausal.PartialQueries
