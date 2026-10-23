import BinaryPhysicalGame

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

Substantive lower-bound endpoint correction: when no target is available,
the ORIGINAL literal union-of-indicator TCM is empty for every source.
Its full class image is constant, so zero queries suffice. This does not
redefine the target by adjoining an observational MAG. The original upper
bound remains valid but need not be sharp at this degenerate endpoint.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget FiniteTargetImage TranscriptDecoder ProfileRegistry
open GProgram.G7.ExactLawResourceGame

universe u

def emptyMarkedGraph (V : Type*) : MarkedGraph V where
  edge _ _ _ _ := False

theorem no_targets_tcm_empty {X S L : Type u} (D : SourceDAG X S L)
    (T : X → Prop) (noneAvailable : ∀ x, ¬ T x) :
    tcm D T = emptyMarkedGraph (CombinedVertex X T) := by
  apply markedGraph_eq
  intro a b ma mb
  constructor
  · rintro ⟨_, t, _⟩
    exact noneAvailable t.val t.property
  · exact False.elim

theorem no_targets_classTarget_constant {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (noneAvailable : ∀ x, ¬ T x)
    (D E : FiniteSource X) : classTarget T D = classTarget T E := by
  apply Finset.ext
  intro code
  rw [classTarget_mem, classTarget_mem]
  have transport (D E : FiniteSource X) :
      (∃ F : FiniteSource X, SameSetwiseSignature T D F ∧ tcm F.dag T = decodeTarget code) →
        ∃ F : FiniteSource X, SameSetwiseSignature T E F ∧ tcm F.dag T = decodeTarget code := by
    rintro ⟨F, signature, target⟩
    exact ⟨E, (SameElementarySignature.refl T E).setwise,
      (no_targets_tcm_empty E.dag T noneAvailable).trans
        ((no_targets_tcm_empty F.dag T noneAvailable).symm.trans target)⟩
  exact ⟨transport D E, transport E D⟩

/-- The class is a SINGLETON empty graph, not an empty set of candidates. -/
theorem no_targets_class_image_singleton {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (noneAvailable : ∀ x, ¬ T x)
    (D : FiniteSource X) (G : MarkedGraph (CombinedVertex X T)) :
    (∃ code ∈ classTarget T D, decodeTarget code = G) ↔
      G = emptyMarkedGraph (CombinedVertex X T) := by
  rw [classTarget_image_exact]
  constructor
  · rintro ⟨E, signature, same⟩
    exact same.symm.trans (no_targets_tcm_empty E.dag T noneAvailable)
  · intro same
    exact ⟨D, (SameElementarySignature.refl T D).setwise,
      (no_targets_tcm_empty D.dag T noneAvailable).trans same.symm⟩

/-- Literal G7 zero-query plan for this target, not a query-count metaphor.
The fixed representative D merely supplies the constant output code set. -/
theorem no_targets_zero_query_valid {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (noneAvailable : ∀ x, ¬ T x) (D : FiniteSource X) :
    Valid (originalGame T)
      (Plan.stop (n := 0) (classTarget T D)) [] 0 := by
  intro E consistent
  exact no_targets_classTarget_constant T noneAvailable E D

theorem no_targets_zero_query_winning {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (noneAvailable : ∀ x, ¬ T x) (D : FiniteSource X) :
    Winning (originalGame T) 0 [] 0 :=
  valid_implies_winning (originalGame T) (.«stop» (classTarget T D)) [] 0
    (no_targets_zero_query_valid T noneAvailable D)

end RestrictedCausal.PartialQueries
