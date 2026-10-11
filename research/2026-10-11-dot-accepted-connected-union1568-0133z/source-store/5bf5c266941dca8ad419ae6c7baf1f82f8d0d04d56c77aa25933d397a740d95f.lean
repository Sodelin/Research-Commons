import G1CanonicalCompletedFutureRootAdmission
import G1UnrankedExteriorHistoryKInsertion

/-! The whole actual exterior unranked checkpoint history is retained through
K-only insertion and ACTUAL unbounded original-root completion.
Contributor: dot, 2026-10-03. -/
namespace G1CompletedExteriorHistoryKInsertion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open G1ActualJointProgram G1ActualJointEpoch G1ActualJointOpaqueContext G1ActualJointStageHistory
open G1UnrankedSourceView G1ActualUnrankedKMacro G1ActualKProductInsertion
open G1UnrankedExteriorHistoryKInsertion G1ActualCompletedKInsertion
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The SAME exterior causal history, unranked current-root K and SAME
original register enter the SAME actual future and unbounded ancestral
completion. Future private choices are fresh; exterior history is not replaced
by a newly sampled marginal. Within-epoch time readers are excluded. -/
theorem actual_completed_K_whole_exterior_history {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (p : Location V E) (phase future : List (ProgramStep N))
    (s : Code N sample) (hi : inside ⊆ (state s).live)
    (sep : SeparatedAgenda N r inside outside phase s)
    (physical : ∀ d ∈ (sourceProgram N r phase s).support, PhysicalKExit N inside outside p d)
    (rootSupport : ∀ d ∈ (sourceProgram N r phase s).support,
      ∀ z ∈ (sourceProgram N r future d).support, AncestralRoot N z)
    (readout : List (UnrankedView V E Copy) → UnrankedView V E Copy → Obs) :
    (sourceStageHistory N r phase s).bind (fun tr =>
      ((sourceProgram N r future (tr.getLastD s)).bind (completionKernel N r)).map
        (fun d => readout (exteriorHistory N outside tr)
          (unrankedView (selectedView (state d) (inside ∪ outside))))) =
      (independentProduct (actualCurrentRootK N r phase s inside hi)
        ((sourceStageHistory N r phase s).map (exteriorHistory N outside))).bind
          (fun data => completedKContinuation N r inside outside phase future s (readout data.2)
            (data.1,data.2.getLastD (unrankedView (selectedView (state s) outside)))) := by
  rw [← actual_K_whole_exterior_history_product N r inside outside phase s hi sep,PMF.bind_map]
  apply bind_eq_of_eq_on_support
  intro tr ht
  have hd : tr.getLastD s ∈ (sourceProgram N r phase s).support := by
    rw [← actual_source_history_end N r phase s]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨tr,ht,rfl⟩
  have he : (exteriorHistory N outside tr).getLastD
      (unrankedView (selectedView (state s) outside)) =
      unrankedView (selectedView (state (tr.getLastD s)) outside) := List.getLastD_map
  simp only [Function.comp_apply,he]
  exact (actual_completed_K_continuation N r inside outside p phase future s
    (tr.getLastD s) hd physical rootSupport (readout (exteriorHistory N outside tr))).symm

#print axioms actual_completed_K_whole_exterior_history
end G1CompletedExteriorHistoryKInsertion
