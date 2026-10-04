import G1ActualUnrankedAncestralCompletion

/-! The SAME original future followed by ACTUAL unbounded ancestral
completion factors through the rooted labelled unranked interface.
Contributor: dot, 2026-10-03. Root support is physical and explicit. -/
namespace G1ActualUnrankedCompletedFuture
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ContextualForestReplacement G1UnrankedSourceView G1UnrankedActualGenerator
open G1ActualJointProgram
open G1UnrankedActualFuture G1ActualUnrankedAncestralCompletion
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def unrankedCompletionRow {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (v : UnrankedIndex N sample keep) : PMF Obs :=
  if h : ∃ s : Code N sample, AncestralRoot N s ∧ unrankedProjection N keep s = v then
    (completionKernel N r (Classical.choose h)).map
      (fun d => readout (unrankedView (selectedView (state d) keep)))
  else PMF.pure (readout v.val)

theorem actual_unranked_completion_projection {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (keep : Finset Copy) (s : Code N sample) (hs : AncestralRoot N s)
    (readout : UnrankedView V E Copy → Obs) :
    unrankedCompletionRow N r keep readout (unrankedProjection N keep s) =
      (completionKernel N r s).map
        (fun d => readout (unrankedView (selectedView (state d) keep))) := by
  have hw : ∃ z : Code N sample, AncestralRoot N z ∧
      unrankedProjection N keep z = unrankedProjection N keep s := ⟨s,hs,rfl⟩
  rw [unrankedCompletionRow,dif_pos hw]
  obtain ⟨hz,hview⟩ := Classical.choose_spec hw
  exact actual_unranked_completion_row N r keep (Classical.choose hw) s hz hs
    (congrArg Subtype.val hview) readout

theorem actual_unranked_completed_future_law {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (keep : Finset Copy) (future : List (ProgramStep N)) (s : Code N sample)
    (rootSupport : ∀ d ∈ (sourceProgram N r future s).support, AncestralRoot N d)
    (readout : UnrankedView V E Copy → Obs) :
    ((sourceProgram N r future s).bind (completionKernel N r)).map
      (fun d => readout (unrankedView (selectedView (state d) keep))) =
      (unrankedProgram N r keep future (unrankedProjection N keep s)).bind
        (unrankedCompletionRow N r keep readout) := by
  rw [PMF.map_bind,← actual_unranked_source_program N r keep future s,PMF.bind_map]
  apply bind_eq_of_eq_on_support
  intro d hd
  exact (actual_unranked_completion_projection N r keep d (rootSupport d hd) readout).symm

/-- Both compared actual futures reach the original ancestral population;
their subsequent ACTUAL unbounded completions have identical full unranked
observer rows. No desired terminal law/equality is a hypothesis. -/
theorem actual_same_original_completed_future_row {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (keep : Finset Copy) (future : List (ProgramStep N)) (s z : Code N sample)
    (hs : ∀ d ∈ (sourceProgram N r future s).support, AncestralRoot N d)
    (hz : ∀ d ∈ (sourceProgram N r future z).support, AncestralRoot N d)
    (hview : unrankedView (selectedView (state s) keep) =
      unrankedView (selectedView (state z) keep)) (readout : UnrankedView V E Copy → Obs) :
    ((sourceProgram N r future s).bind (completionKernel N r)).map
      (fun d => readout (unrankedView (selectedView (state d) keep))) =
    ((sourceProgram N r future z).bind (completionKernel N r)).map
      (fun d => readout (unrankedView (selectedView (state d) keep))) := by
  rw [actual_unranked_completed_future_law N r keep future s hs,
    actual_unranked_completed_future_law N r keep future z hz]
  have he : unrankedProjection N keep s = unrankedProjection N keep z := Subtype.ext hview
  rw [he]

#print axioms actual_same_original_completed_future_row
end G1ActualUnrankedCompletedFuture
