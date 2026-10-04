import G1SourceMacroInterfaceHistory

/-! Repeated source-derived K substitutions followed by the SAME original
future and actual unbounded ancestral completion, retaining the whole original
unranked checkpoint trajectory. Root admission is physical and explicit.
Contributor: dot, 2026-10-03. -/
namespace G1SourceMacroActualCompletion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open G1ContextualForestReplacement G1ActualJointProgram
open G1SameOriginalExteriorContinuation
open G1UnrankedSourceView G1UnrankedActualGenerator G1UnrankedActualFuture
open G1ActualUnrankedCompletedFuture G1OriginalWholeCausalView
open G1SourceMacroComposition G1SourceMacroInterfaceHistory
open scoped Classical
variable {V E X Copy Obs : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Merely packages an actual whole-view value as the finite derived source
quotient index. No raw source representative is resampled here. -/
noncomputable def wholeViewIndex (N : RootedBinary V E X) {sample : Copy → X}
    (fallback : Code N sample) (v : UnrankedView V E Copy) : UnrankedIndex N sample Finset.univ :=
  if h : ∃ s : Code N sample, wholeOriginalView N s = v then ⟨v,h⟩
  else unrankedProjection N Finset.univ fallback

lemma wholeViewIndex_at_actual (N : RootedBinary V E X) {sample : Copy → X}
    (fallback s : Code N sample) :
    wholeViewIndex N fallback (wholeOriginalView N s) = unrankedProjection N Finset.univ s := by
  have hs : ∃ z : Code N sample, wholeOriginalView N z = wholeOriginalView N s := ⟨s,rfl⟩
  rw [wholeViewIndex,dif_pos hs]
  rfl

/-- The terminal observer is constructed from the ACTUAL original quotient
program and its ACTUAL root-admitted completion row. The fallback cannot affect
an actual source interface; no arbitrary supplied exterior output law occurs. -/
noncomputable def actualCompletedTerminal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (future : List (ProgramStep N)) (fallback : Code N sample)
    (readout : UnrankedView V E Copy → Obs) (v : UnrankedView V E Copy) : PMF Obs :=
  (unrankedProgram N r Finset.univ future (wholeViewIndex N fallback v)).bind
    (unrankedCompletionRow N r Finset.univ readout)

theorem actual_completed_terminal_at_source (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (future : List (ProgramStep N)) (fallback s : Code N sample)
    (rootSupport : ∀ d ∈ (sourceProgram N r future s).support, AncestralRoot N d)
    (readout : UnrankedView V E Copy → Obs) :
    actualCompletedTerminal N r future fallback readout (wholeOriginalView N s) =
      ((sourceProgram N r future s).bind (completionKernel N r)).map
        (fun d => readout (wholeOriginalView N d)) := by
  rw [actualCompletedTerminal,wholeViewIndex_at_actual]
  exact (actual_unranked_completed_future_law N r Finset.univ future s rootSupport readout).symm

/-- Macro representatives are REAL source-support states. Therefore the
physical root admission of the concatenated ORIGINAL program transfers to the
actual future/completion after every macro, without a new root hypothesis on
invented states or a claimed equality of raw Code laws. -/
theorem actual_repeated_macro_same_completed_future (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (stages : List (SourceMacroStage N sample r))
    (future : List (ProgramStep N)) (initial : Code N sample)
    (rootSupport : ∀ d ∈ (sourceProgram N r (literalProgram N r stages) initial).support,
      ∀ z ∈ (sourceProgram N r future d).support, AncestralRoot N z)
    (readout : UnrankedView V E Copy → Obs) :
    ((sourceMacroInterpreter N r stages initial).bind
      (fun d => (sourceProgram N r future d).bind (completionKernel N r))).map
        (fun d => readout (wholeOriginalView N d)) =
    ((sourceProgram N r (literalProgram N r stages ++ future) initial).bind
      (completionKernel N r)).map (fun d => readout (wholeOriginalView N d)) := by
  have hm : (sourceMacroInterpreter N r stages initial).bind
      (fun d => ((sourceProgram N r future d).bind (completionKernel N r)).map
        (fun z => readout (wholeOriginalView N z))) =
      ((sourceMacroInterpreter N r stages initial).map (wholeOriginalView N)).bind
        (actualCompletedTerminal N r future initial readout) := by
    rw [PMF.bind_map]
    apply bind_eq_of_eq_on_support
    intro d hd
    exact (actual_completed_terminal_at_source N r future initial d
      (rootSupport d (actual_repeated_macro_support N r stages initial hd)) readout).symm
  rw [PMF.map_bind]
  rw [hm,actual_repeated_source_K_macro_interpreter,PMF.bind_map]
  rw [actual_source_program_append,PMF.bind_bind,PMF.map_bind]
  apply bind_eq_of_eq_on_support
  intro d hd
  exact actual_completed_terminal_at_source N r future initial d (rootSupport d hd) readout

noncomputable def actualPhysicalCompletedHistory (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (future : List (ProgramStep N))
    (readout : UnrankedView V E Copy → Obs) : List (SourceMacroStage N sample r) →
      Code N sample → PMF (InterfaceHistory V E Copy Obs)
  | [],s => (((sourceProgram N r future s).bind (completionKernel N r)).map
      (fun d => readout (wholeOriginalView N d))).map (fun x => ([],x))
  | a::as,s => (sourceProgram N r a.phase s).bind
      (fun d => (actualPhysicalCompletedHistory N r future readout as d).map
        (prependView (wholeOriginalView N d)))

lemma actual_history_terminal_is_completed (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (stages : List (SourceMacroStage N sample r))
    (future : List (ProgramStep N)) (fallback initial : Code N sample)
    (rootSupport : ∀ d ∈ (sourceProgram N r (literalProgram N r stages ++ future) initial).support,
      AncestralRoot N d) (readout : UnrankedView V E Copy → Obs) :
    actualOriginalInterfaceHistory N r (actualCompletedTerminal N r future fallback readout) stages initial =
      actualPhysicalCompletedHistory N r future readout stages initial := by
  induction stages generalizing initial with
  | nil =>
    simp only [actualOriginalInterfaceHistory,actualPhysicalCompletedHistory]
    rw [actual_completed_terminal_at_source N r future fallback initial
      (by simpa [literalProgram] using rootSupport)]
  | cons a as ih =>
    rw [actualOriginalInterfaceHistory,actualPhysicalCompletedHistory]
    apply bind_eq_of_eq_on_support
    intro d hd
    have hr : ∀ z ∈ (sourceProgram N r (literalProgram N r as ++ future) d).support,
        AncestralRoot N z := by
      intro z hz
      apply rootSupport z
      simp only [literalProgram,List.flatMap_cons,List.append_assoc]
      rw [actual_source_program_append]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨d,hd,hz⟩
    rw [ih d hr]

/-- Final derived JOINT law: every original unranked interface checkpoint,
the SAME original future and actual unbounded completion. No desired target law
or fitted continuation is supplied; the sole final admission is physical root
support of the literal original source program. -/
theorem actual_repeated_macro_completed_whole_history (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (stages : List (SourceMacroStage N sample r))
    (future : List (ProgramStep N)) (initial : Code N sample)
    (rootSupport : ∀ d ∈ (sourceProgram N r (literalProgram N r stages ++ future) initial).support,
      AncestralRoot N d) (readout : UnrankedView V E Copy → Obs) :
    sourceMacroInterfaceHistory N r (actualCompletedTerminal N r future initial readout) stages initial =
      actualPhysicalCompletedHistory N r future readout stages initial := by
  rw [actual_repeated_macro_whole_interface_history]
  exact actual_history_terminal_is_completed N r stages future initial initial rootSupport readout

#print axioms actual_repeated_macro_same_completed_future
#print axioms actual_repeated_macro_completed_whole_history
end G1SourceMacroActualCompletion
