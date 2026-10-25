import BinaryPhysicalOracle
import RestrictedQueryBudgetBound

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Full selected binary physical-source/G7 upper-policy composition. The
response is the actual elementary population CI or selected conditional
regime-law comparison. ExactResponse is discharged by the preceding
probability and original-label proof bodies, not retained as an oracle
premise. One PhysicalSource is fixed across the whole interactive run.

The target remains the ENTIRE original finite-source marked HPL TCM
equivalence class on ALL observed labels. Arbitrary finite selection and
latent carriers are quantified in that target and all have common positive
binary representatives. The explicit supplied-label policy and exact B
budget are unchanged. This is not a sample or intervention-count theorem.

Every transitive body, including the Lean 4.33.1 G7 compatibility port,
remains unelaborated. No machine verification or new novelty is claimed.
-/

namespace RestrictedCausal.PhysicalSource

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget FiniteTargetImage TranscriptDecoder PartialQueries ProfileRegistry
open GProgram.G7.ExactLawResourceGame

universe u

variable {X : Type u} [LinearOrder X] [Fintype X]
variable (T : X → Prop) [DecidablePred T]

noncomputable def physicalGame :
    Experiment (PhysicalSource T) (ElementaryAction X T) Bool (Finset (TargetCode X T)) Nat :=
  sourceGame T (fun P : PhysicalSource T => P.graph) (physicalResponse T)

/-- Legality and resource validity hold on every Boolean response branch,
including branches inconsistent with any physical source. -/
theorem physical_restricted_plan_valid :
    Valid (physicalGame T) (effectiveRestrictedPlan T) [] (coordinateBudget T) :=
  effectiveRestrictedPlan_valid T (fun P : PhysicalSource T => P.graph)
    (physicalResponse T) (physical_response_exact T)

theorem physical_restricted_plan_identifies (P : PhysicalSource T) :
    run (physicalGame T) (effectiveRestrictedPlan T) P = classTarget T P.graph :=
  effectiveRestrictedPlan_identifies_exact_response T (fun P : PhysicalSource T => P.graph)
    (physicalResponse T) (physical_response_exact T) P

/-- Expanded final target, with one original rival E shared across every
named intervention. No product of independently realizable slice classes. -/
theorem physical_restricted_plan_full_target (P : PhysicalSource T)
    (G : MarkedGraph (CombinedVertex X T)) :
    (∃ b ∈ run (physicalGame T) (effectiveRestrictedPlan T) P, decodeTarget b = G) ↔
      ∃ E : FiniteSource X, SameSetwiseSignature T P.graph E ∧ tcm E.dag T = G := by
  rw [physical_restricted_plan_identifies]
  exact classTarget_image_exact T P.graph G

/-- No original finite graph is silently excluded from the statistical
source realization class. This is mathematical rational existence, not a
numerically executed CPT construction. -/
theorem every_original_source_has_physical_run (D : FiniteSource X) :
    ∃ P : PhysicalSource T, P.graph = D ∧
      run (physicalGame T) (effectiveRestrictedPlan T) P = classTarget T D := by
  exact ⟨realize T D, rfl, physical_restricted_plan_identifies T (realize T D)⟩

/-- Full original-source selected upper outcome. Physical realization is
derived for the given D; graph equivalence is the original all-observed
marked-class target; the policy and paid query horizon are unchanged. -/
theorem original_selected_binary_upper (D : FiniteSource X) :
    ∃ P : PhysicalSource T, P.graph = D ∧
      Valid (physicalGame T) (effectiveRestrictedPlan T) [] (coordinateBudget T) ∧
      (∀ G : MarkedGraph (CombinedVertex X T),
        (∃ b ∈ run (physicalGame T) (effectiveRestrictedPlan T) P, decodeTarget b = G) ↔
          ∃ E : FiniteSource X, SameSetwiseSignature T D E ∧ tcm E.dag T = G) ∧
      2 * coordinateBudget T ≤
        5 * Fintype.card X * (Fintype.card X - 1) * 2 ^ Fintype.card {x : X // ¬ T x} := by
  refine ⟨realize T D, rfl, physical_restricted_plan_valid T, ?_, coordinate_budget_bound T⟩
  intro G
  exact physical_restricted_plan_full_target T (realize T D) G

end RestrictedCausal.PhysicalSource
