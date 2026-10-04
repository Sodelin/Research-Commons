import G1RepeatedOriginalExteriorHistoryMacros

/-! Complete within-phase ORIGINAL exterior checkpoint histories through
repeated true K macros and SAME actual original future/unbounded completion.
Contributor: dot, 2026-10-03. -/
namespace G1RepeatedExteriorHistoryActualCompletion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open G1ActualJointProgram G1SameOriginalExteriorContinuation G1ActualJointStageHistory
open G1UnrankedSourceView G1OriginalWholeCausalView G1OriginalHistoryQuotient
open G1ActualHistoryEnrichedKMacro G1RepeatedOriginalExteriorHistoryMacros
open G1SourceMacroActualCompletion
open scoped Classical
variable {V E X Copy Obs : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def historyLiteralProgram (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (stages : List (OriginalHistoryStage N sample r)) : List (ProgramStep N) :=
  stages.flatMap OriginalHistoryStage.phase

lemma actual_original_observed_phase_end_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (outside : Finset Copy)
    (s : Code N sample) {out : List (UnrankedView V E Copy) × Code N sample}
    (hout : out ∈ (originalObservedPhaseRow N r phase outside s).support) :
    out.2 ∈ (sourceProgram N r phase s).support := by
  obtain ⟨tr,ht,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact real_history_end_support N r phase s tr ht

noncomputable def actualPhysicalCompletedExteriorHistories (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (future : List (ProgramStep N))
    (readout : UnrankedView V E Copy → Obs) : List (OriginalHistoryStage N sample r) →
      Code N sample → PMF (FullExteriorHistory V E Copy Obs)
  | [],s => (((sourceProgram N r future s).bind (completionKernel N r)).map
      (fun d => readout (wholeOriginalView N d))).map (fun o => ([],o))
  | a::as,s => (originalObservedPhaseRow N r a.phase a.observedOutside s).bind
      (fun out => (actualPhysicalCompletedExteriorHistories N r future readout as out.2).map
        (prependPhaseHistory out.1))

lemma actual_original_history_terminal_completion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (stages : List (OriginalHistoryStage N sample r))
    (future : List (ProgramStep N)) (fallback initial : Code N sample)
    (rootSupport : ∀ d ∈ (sourceProgram N r (historyLiteralProgram N r stages ++ future) initial).support,
      AncestralRoot N d) (readout : UnrankedView V E Copy → Obs) :
    actualOriginalHistoryRun N r (actualCompletedTerminal N r future fallback readout) stages initial =
      actualPhysicalCompletedExteriorHistories N r future readout stages initial := by
  induction stages generalizing initial with
  | nil =>
    simp only [actualOriginalHistoryRun,actualPhysicalCompletedExteriorHistories]
    rw [actual_completed_terminal_at_source N r future fallback initial
      (by simpa [historyLiteralProgram] using rootSupport)]
  | cons a as ih =>
    rw [actualOriginalHistoryRun,actualPhysicalCompletedExteriorHistories]
    apply bind_eq_of_eq_on_support
    intro out hout
    have he := actual_original_observed_phase_end_support N r a.phase a.observedOutside initial hout
    have hr : ∀ z ∈ (sourceProgram N r (historyLiteralProgram N r as ++ future) out.2).support,
        AncestralRoot N z := by
      intro z hz
      apply rootSupport z
      simp only [historyLiteralProgram,List.flatMap_cons,List.append_assoc]
      rw [actual_source_program_append]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨out.2,he,hz⟩
    rw [ih out.2 hr]

/-- Exact JOINT source result at the stronger accepted G1 interface: all
original exterior descendant-labelled agenda checkpoints across every macro,
SAME original future and actual unbounded ancestral completion. Physical
canonical admission is separate; no fitted desired output law is supplied. -/
theorem actual_repeated_K_original_exterior_histories_completed_future (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (stages : List (OriginalHistoryStage N sample r))
    (future : List (ProgramStep N)) (initial : Code N sample)
    (rootSupport : ∀ d ∈ (sourceProgram N r (historyLiteralProgram N r stages ++ future) initial).support,
      AncestralRoot N d) (readout : UnrankedView V E Copy → Obs) :
    historyEnrichedMacroRun N r (actualCompletedTerminal N r future initial readout) stages initial =
      actualPhysicalCompletedExteriorHistories N r future readout stages initial := by
  rw [actual_repeated_K_full_original_exterior_history]
  exact actual_original_history_terminal_completion N r stages future initial initial rootSupport readout

/-- The whole original completed forest observer is recovered from the full
original causal quotient, including every old carried subtree and root clade. -/
theorem actual_completed_forest_from_whole_view (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) :
    G1ContextualForestReplacement.rootForest N s = G1UnrankedActualFuture.unrankedViewForest (wholeOriginalView N s) := by
  rw [←whole_forest_eq]
  exact G1UnrankedActualFuture.actual_unranked_view_forest _

#print axioms actual_repeated_K_original_exterior_histories_completed_future
end G1RepeatedExteriorHistoryActualCompletion
