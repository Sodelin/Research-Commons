import BinaryFaithfulInvariance
import RestrictedInteractivePlan

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Application-level label adapter. The original observed, selection and
latent carriers are unchanged; both hidden carriers are arbitrary finite
types supplied by FiniteSource. The separate indicator's Option carrier
is explicitly isomorphic to augmentSource's original sum carrier.
No numerical-law equality under graph equivalence is asserted here.
-/

namespace RestrictedCausal.PhysicalSource

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget FiniteTargetImage FiniteGraphDecision TranscriptDecoder GraphEquivalence
open ProbabilitySource ProbabilitySource.BinaryCPT

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

abbrev OriginalVertex (D : FiniteSource X) := SourceVertex X D.selections D.latents

noncomputable instance originalVertexFintype (D : FiniteSource X) : Fintype (OriginalVertex D) := by
  letI := D.selectionFintype
  letI := D.latentFintype
  infer_instance

noncomputable instance originalVertexDecidableEq (D : FiniteSource X) : DecidableEq (OriginalVertex D) :=
  Classical.decEq _

noncomputable def originalSelection (D : FiniteSource X) : Finset (OriginalVertex D) := by
  classical
  exact Finset.univ.filter Selected

noncomputable def originalCondition (D : FiniteSource X) (b : X → Bool) : Finset (OriginalVertex D) := by
  classical
  exact Finset.univ.filter (SelectedCondition (BoolCondition b))

theorem original_selection_mem (D : FiniteSource X) (v : OriginalVertex D) :
    v ∈ originalSelection D ↔ Selected v := by
  classical
  simp only [originalSelection, Finset.mem_filter, Finset.mem_univ, true_and]

theorem original_condition_mem (D : FiniteSource X) (b : X → Bool) (v : OriginalVertex D) :
    v ∈ originalCondition D b ↔ SelectedCondition (BoolCondition b) v := by
  classical
  simp only [originalCondition, Finset.mem_filter, Finset.mem_univ, true_and]

theorem original_selection_sinks (D : FiniteSource X) :
    ∀ s ∈ originalSelection D, ∀ v, ¬ D.dag.arrow s v := by
  intro s member v
  have selected := (original_selection_mem D s).mp member
  rcases s with ((x | s) | l)
  · exact selected.elim
  · exact D.dag.selection_sink s v
  · exact selected.elim

theorem original_selection_contained (D : FiniteSource X) (b : X → Bool) :
    originalSelection D ⊆ originalCondition D b := by
  intro v member
  apply (original_condition_mem D b v).mpr
  have selected := (original_selection_mem D v).mp member
  rcases v with ((x | s) | l)
  · exact selected.elim
  · trivial
  · exact selected.elim

theorem observed_outside_original_condition (D : FiniteSource X) (b : X → Bool) (x : X)
    (outside : ¬ BoolCondition b x) : Observed x ∉ originalCondition D b := by
  intro member
  exact outside ((original_condition_mem D b (Observed x)).mp member)

theorem original_condition_predicate (D : FiniteSource X) (b : X → Bool) :
    (fun v => v ∈ originalCondition D b) = SelectedCondition (BoolCondition b) :=
  funext (fun v => propext (original_condition_mem D b v))

/-- After deleting the constant selection flags, the conditioning set
contains exactly the queried observed labels and no latent coordinate. -/
theorem original_observed_condition_members (D : FiniteSource X) (b : X → Bool)
    (v : OriginalVertex D) :
    v ∈ originalCondition D b \ originalSelection D ↔
      ∃ x : X, v = Observed x ∧ BoolCondition b x := by
  rw [Finset.mem_sdiff, original_condition_mem, original_selection_mem]
  rcases v with ((x | s) | l)
  · constructor
    · intro h
      exact ⟨x, rfl, h.1⟩
    · rintro ⟨y, same, conditioned⟩
      have equal : x = y := Sum.inl.inj (Sum.inl.inj same)
      subst y
      exact ⟨conditioned, fun «impossible» => «impossible»⟩
  · constructor
    · intro h; exact (h.2 True.intro).elim
    · rintro ⟨y, «impossible», _⟩; cases «impossible»
  · constructor
    · intro h; exact h.1.elim
    · rintro ⟨y, «impossible», _⟩; cases «impossible»

def originalIndicatorEquiv (D : FiniteSource X) (target : X) :
    MarkedEquiv (arrowGraph (augmentSource D.dag target).arrow)
      (arrowGraph (AddIndicator D.dag.arrow (Observed target))) where
  toEquiv := sourceIndicatorEquiv
  edge _ _ _ _ := Iff.rfl

theorem original_indicator_condition (D : FiniteSource X) (b : X → Bool)
    (v : SourceVertex (Option X) D.selections D.latents) :
    SelectedCondition (InvarianceCondition (BoolCondition b)) v ↔
      sourceIndicatorEquiv v ∈ (originalCondition D b).image some := by
  have oldImage : ∀ old : OriginalVertex D,
      some old ∈ (originalCondition D b).image some ↔ SelectedCondition (BoolCondition b) old := by
    intro old
    constructor
    · intro member
      obtain ⟨preimage, original, same⟩ := Finset.mem_image.mp member
      have equal := Option.some.inj same
      subst preimage
      exact (original_condition_mem D b old).mp original
    · intro conditioned
      exact Finset.mem_image.mpr ⟨old, (original_condition_mem D b old).mpr conditioned, rfl⟩
  rcases v with ((x | s) | l)
  · cases x with
    | none =>
        constructor
        · intro «impossible»; exact «impossible».elim
        · intro member
          obtain ⟨_, _, «impossible»⟩ := Finset.mem_image.mp member
          cases «impossible»
    | some x => exact (oldImage (Observed x)).symm
  · exact (oldImage (.inl (.inr s))).symm
  · exact (oldImage (.inr l)).symm

theorem original_indicator_connection (D : FiniteSource X) (target x : X) (b : X → Bool) :
    ActiveConnection (arrowGraph (augmentSource D.dag target).arrow)
      (SelectedCondition (InvarianceCondition (BoolCondition b))) (Observed none) (Observed (some x)) ↔
    ActiveConnection (arrowGraph (AddIndicator D.dag.arrow (Observed target)))
      (fun v => v ∈ (originalCondition D b).image some) none (some (Observed x)) :=
  (originalIndicatorEquiv D target).active_iff (original_indicator_condition D b) _ _

end RestrictedCausal.PhysicalSource
