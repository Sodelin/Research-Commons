import G1ActualCompletedKInsertion

/-! Actual original opaque subtrees survive every winner jump and ancestral
completion, closing the original-forest observer binding beyond finite source
programs. Contributor: dot, 2026-10-03. -/
namespace G1OriginalCompletedForestReconstruction
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ContextualForestReplacement G1OriginalCurrentRootReconstruction
open G1OpaqueSourceGrafting G1ActualJointProgram G1SameOriginalExteriorContinuation
open G1ActualJointEpoch
open G1UnrankedSourceView G1UnrankedActualFuture G1ActualUnrankedKMacro
open G1ActualKProductInsertion G1ActualCompletedKInsertion
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_completion_reconstruction_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (input : Copy → Genealogy Copy) (keep : Finset Copy)
    (n : Nat) (s : Code N sample) (hs : Reconstructs input keep (state s))
    {d : Code N sample} (hd : d ∈ (ancestralCompletion N r n s).support) :
    Reconstructs input keep (state d) := by
  induction n generalizing s d with
  | zero =>
      have he : d = s := by simpa [ancestralCompletion] using hd
      subst d
      exact hs
  | succ n ih =>
      obtain ⟨z,hz,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have hr : Reconstructs input keep (state z) := by
        rcases source_jump_support_cases N r s hz with ⟨he,_⟩ | ⟨p,he⟩
        · simpa [he] using hs
        · rw [he]
          exact actual_step_reconstruction N input keep s hs (some p)
      exact ih z hr hd

/-- EXISTING full original-descendant forest, including the inherited actual
winner-jump completion kernel, equals grafting every original entering subtree
into the current-root forest. Its unbounded ancestral interpretation is proved
separately under physical root support. No reconstruction equality is assumed. -/
theorem actual_original_completed_forest_law
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (s : Code N sample) :
    ((sourceProgram N r ops s).bind (completionKernel N r)).map (rootForest N) =
      ((sourceProgram N r ops s).bind (completionKernel N r)).map
        (fun d => (sourceUnrankedForest (state d) (state s).live).image
          (graftUnranked (state s).genealogy)) := by
  apply map_eq_of_eq_on_support
  intro d hd
  obtain ⟨z,hz,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_whole_forest_reconstruction N (state s).genealogy (state s).live d
    (actual_completion_reconstruction_support N r _ _ (Fintype.card Copy) z
      (actual_program_reconstruction_support N r ops s hz) hd)

theorem actual_original_completed_K_product_insertion
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (p : Location V E) (phase future : List (ProgramStep N))
    (s : Code N sample) (hi : inside ⊆ (state s).live) (ho : outside ⊆ (state s).live)
    (partition : inside ∪ outside = (state s).live)
    (sep : SeparatedAgenda N r inside outside phase s)
    (physical : ∀ d ∈ (sourceProgram N r phase s).support, PhysicalKExit N inside outside p d)
    (rootSupport : ∀ d ∈ (sourceProgram N r phase s).support,
      ∀ z ∈ (sourceProgram N r future d).support, AncestralRoot N z) :
    ((sourceProgram N r (phase ++ future) s).bind (completionKernel N r)).map (rootForest N) =
      (independentProduct (actualCurrentRootK N r phase s inside hi)
        (actualExteriorUnrankedState N r phase s outside ho)).bind
          (completedKContinuation N r inside outside phase future s
            (fun v => (unrankedViewForest v).image (graftUnranked (state s).genealogy))) := by
  rw [actual_original_completed_forest_law]
  simpa only [partition,sourceUnrankedForest,actual_unranked_view_forest] using
    (actual_completed_K_product_insertion N r inside outside p phase future s hi ho sep physical
      rootSupport (fun v => (unrankedViewForest v).image (graftUnranked (state s).genealogy)))

#print axioms actual_original_completed_K_product_insertion
end G1OriginalCompletedForestReconstruction
