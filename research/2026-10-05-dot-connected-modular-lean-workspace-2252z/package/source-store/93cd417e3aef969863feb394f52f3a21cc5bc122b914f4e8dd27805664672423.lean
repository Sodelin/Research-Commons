import G1ActualUnrankedCompletedFuture
import G1ActualKProductInsertion

/-! K-only insertion into the SAME actual original future followed by its
ACTUAL unbounded ancestral completion. Representatives are restricted to
REAL phase support. Contributor: dot, 2026-10-03. -/
namespace G1ActualCompletedKInsertion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ActualJointProgram G1ActualJointEpoch G1ActualJointOpaqueContext
open G1SameOriginalExteriorContinuation
open G1UnrankedSourceView G1UnrankedActualFuture G1UnrankedSingleExitLabel
open G1ActualUnrankedKMacro G1ActualKProductInsertion G1ActualUnrankedCompletedFuture
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def completedKContinuation {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (phase future : List (ProgramStep N))
    (initial : Code N sample) (readout : UnrankedView V E Copy → Obs)
    (data : KExitData V E Copy) : PMF Obs :=
  if h : ∃ s : Code N sample, s ∈ (sourceProgram N r phase initial).support ∧
      actualKExitData N inside outside s = data then
    ((sourceProgram N r future (Classical.choose h)).bind (completionKernel N r)).map
      (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside))))
  else ((sourceProgram N r future initial).bind (completionKernel N r)).map
    (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside))))

theorem actual_completed_K_continuation {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (p : Location V E) (phase future : List (ProgramStep N))
    (initial s : Code N sample) (hs : s ∈ (sourceProgram N r phase initial).support)
    (physical : ∀ d ∈ (sourceProgram N r phase initial).support, PhysicalKExit N inside outside p d)
    (rootSupport : ∀ d ∈ (sourceProgram N r phase initial).support,
      ∀ z ∈ (sourceProgram N r future d).support, AncestralRoot N z)
    (readout : UnrankedView V E Copy → Obs) :
    completedKContinuation N r inside outside phase future initial readout
      (actualKExitData N inside outside s) =
      ((sourceProgram N r future s).bind (completionKernel N r)).map
        (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside)))) := by
  have hw : ∃ z : Code N sample, z ∈ (sourceProgram N r phase initial).support ∧
      actualKExitData N inside outside z = actualKExitData N inside outside s := ⟨s,hs,rfl⟩
  rw [completedKContinuation,dif_pos hw]
  obtain ⟨hz,hdata⟩ := Classical.choose_spec hw
  have hK := congrArg Prod.fst hdata
  have ho := congrArg Prod.snd hdata
  have hreg : (state (Classical.choose hw)).register = (state s).register :=
    unranked_view_register _ _ ho
  exact actual_same_original_completed_future_row N r (inside ∪ outside) future
    (Classical.choose hw) s (rootSupport _ hz) (rootSupport s hs)
    (actual_K_only_complete_exit_view _ _ (Classical.choose hw).property.forest s.property.forest
      inside outside p (physical _ hz).1 (physical s hs).1 hK
      (physical _ hz).2 (physical s hs).2 hreg ho) readout

/-- Actual unranked K from the TRUE smaller current-root source, the actual
concurrent exterior state and SAME register determine the SAME original
completed future. Root support is a physical source condition, not an output
law or conclusion supplied as a premise. -/
theorem actual_completed_K_product_insertion {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (p : Location V E) (phase future : List (ProgramStep N))
    (s : Code N sample) (hi : inside ⊆ (state s).live) (ho : outside ⊆ (state s).live)
    (sep : SeparatedAgenda N r inside outside phase s)
    (physical : ∀ d ∈ (sourceProgram N r phase s).support, PhysicalKExit N inside outside p d)
    (rootSupport : ∀ d ∈ (sourceProgram N r phase s).support,
      ∀ z ∈ (sourceProgram N r future d).support, AncestralRoot N z)
    (readout : UnrankedView V E Copy → Obs) :
    ((sourceProgram N r (phase ++ future) s).bind (completionKernel N r)).map
      (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside)))) =
      (independentProduct (actualCurrentRootK N r phase s inside hi)
        (actualExteriorUnrankedState N r phase s outside ho)).bind
          (completedKContinuation N r inside outside phase future s readout) := by
  rw [← actual_K_exterior_interface_product N r inside outside phase s hi ho sep,
    PMF.bind_map,actual_source_program_append,PMF.bind_bind,PMF.map_bind]
  apply bind_eq_of_eq_on_support
  intro d hd
  exact (actual_completed_K_continuation N r inside outside p phase future s d hd physical
    rootSupport readout).symm

#print axioms actual_completed_K_product_insertion
end G1ActualCompletedKInsertion
