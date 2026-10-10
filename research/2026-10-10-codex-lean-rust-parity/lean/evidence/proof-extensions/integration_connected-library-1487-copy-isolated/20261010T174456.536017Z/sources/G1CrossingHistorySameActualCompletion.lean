import G1ActualCrossingWholeExteriorHistory

/-! SAME actual original future/unbounded completion after crossing actors,
retaining every original exterior checkpoint and all original labelled trees.
The final causal view is reconstructed from real pure source panel fibres.
Contributor: dot, 2026-10-03. -/
namespace G1CrossingHistorySameActualCompletion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open G1JointUnrankedForestAssembly G1SameOriginalExteriorContinuation G1SourceMacroActualCompletion
open G1ActualJointProgram G1ActualJointStageHistory G1ActualHistoryEnrichedKMacro
open G1UnrankedSourceView G1OriginalWholeCausalView G1ActualCrossingWholeExteriorHistory
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical
variable {V E X Copy Obs : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev CrossingData (N : RootedBinary V E X) (sample : Copy → X) (left right exterior : Finset Copy) :=
  SelectedIndex N sample left × SelectedIndex N sample right × CrossingRecord N sample left right exterior

noncomputable def crossingMarker (N : RootedBinary V E X) {sample : Copy → X}
    (left right exterior : Finset Copy) (s : Code N sample)
    (first middle last : List (Code N sample)) : CrossingData N sample left right exterior :=
  let p := first.getLastD s
  let q := middle.getLastD p
  let z := last.getLastD q
  (projection N left q,projection N right z,
    (first.map (projection N (right ∪ exterior)),middle.map (projection N exterior),
      last.map (projection N (left ∪ exterior)),projection N (left ∪ exterior) z))

noncomputable def crossingFinalWholeView (N : RootedBinary V E X) {sample : Copy → X}
    (left right exterior : Finset Copy) (data : CrossingData N sample left right exterior) : UnrankedView V E Copy :=
  unrankedView (joinedPanelView right (data.2.1.val,data.2.2.2.2.2.val))

lemma actual_crossing_final_whole_view (N : RootedBinary V E X) {sample : Copy → X}
    (left right exterior : Finset Copy) (hpart : right ∪ (left ∪ exterior) = Finset.univ)
    (s : Code N sample) (first middle last : List (Code N sample))
    (hpure : PrunedPanelSeparated (state (last.getLastD (middle.getLastD (first.getLastD s))))
      right (left ∪ exterior)) :
    crossingFinalWholeView N left right exterior (crossingMarker N left right exterior s first middle last) =
      wholeOriginalView N (last.getLastD (middle.getLastD (first.getLastD s))) := by
  dsimp only [crossingFinalWholeView,crossingMarker]
  have hj := actual_joined_panel_view _
    (last.getLastD (middle.getLastD (first.getLastD s))).property.forest right (left ∪ exterior) hpure
  rw [hpart] at hj
  exact congrArg unrankedView hj.symm

noncomputable def crossingCompletedTerminal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (left right exterior : Finset Copy) (future : List (ProgramStep N))
    (fallback : Code N sample) (readout : UnrankedView V E Copy → Obs)
    (data : CrossingData N sample left right exterior) :=
  (actualCompletedTerminal N r future fallback readout (crossingFinalWholeView N left right exterior data)).map
    (fun out => (data.2.2.1,data.2.2.2.1,data.2.2.2.2.1,out))

noncomputable def actualPhysicalCrossingCompletedHistory (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (left right exterior : Finset Copy)
    (preops concurrent suffix future : List (ProgramStep N)) (s : Code N sample)
    (readout : UnrankedView V E Copy → Obs) :=
  (sourceStageHistory N r preops s).bind (fun first =>
    let p := first.getLastD s
    (sourceStageHistory N r concurrent p).bind (fun middle =>
      let q := middle.getLastD p
      (sourceStageHistory N r suffix q).bind (fun last =>
        let z := last.getLastD q
        (((sourceProgram N r future z).bind (completionKernel N r)).map
          (fun d => readout (wholeOriginalView N d))).map
            (fun out => (first.map (projection N (right ∪ exterior)),middle.map (projection N exterior),
              last.map (projection N (left ∪ exterior)),out)))))

/-- Actual crossing pending rows continue through the SAME original future
and ACTUAL unbounded completion. All exterior paths remain JOINT. Physical
root support is on REAL original chronological source states only. -/
theorem actual_crossing_history_same_completed_future (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (left right exterior : Finset Copy)
    (hpart : right ∪ (left ∪ exterior) = Finset.univ)
    (preops concurrent suffix future : List (ProgramStep N)) (s : Code N sample)
    (prefixSeparate : G1ActualJointProgram.SeparatedAgenda N r left (right ∪ exterior) preops s)
    (concurrentFirst : ∀ p ∈ (sourceProgram N r preops s).support,
      G1ActualJointProgram.SeparatedAgenda N r left (right ∪ exterior) concurrent p)
    (concurrentOthers : ∀ p ∈ (sourceProgram N r preops s).support,
      G1ActualJointProgram.SeparatedAgenda N r right exterior concurrent p)
    (suffixSeparate : ∀ p ∈ (sourceProgram N r preops s).support,
      ∀ q ∈ (sourceProgram N r concurrent p).support,
      G1ActualJointProgram.SeparatedAgenda N r right (left ∪ exterior) suffix q)
    (middlePure : ∀ p ∈ (sourceProgram N r preops s).support,
      ∀ q ∈ (sourceProgram N r concurrent p).support,
      PrunedPanelSeparated (state q) left exterior)
    (finalPure : ∀ p ∈ (sourceProgram N r preops s).support,
      ∀ q ∈ (sourceProgram N r concurrent p).support,
      ∀ z ∈ (sourceProgram N r suffix q).support,
      PrunedPanelSeparated (state z) right (left ∪ exterior))
    (rootSupport : ∀ p ∈ (sourceProgram N r preops s).support,
      ∀ q ∈ (sourceProgram N r concurrent p).support,
      ∀ z ∈ (sourceProgram N r suffix q).support,
      ∀ d ∈ (sourceProgram N r future z).support, AncestralRoot N d)
    (readout : UnrankedView V E Copy → Obs) :
    (actualCrossingPendingHistoryRun N r left right exterior preops concurrent suffix s).bind
      (crossingCompletedTerminal N r left right exterior future s readout) =
      actualPhysicalCrossingCompletedHistory N r left right exterior preops concurrent suffix future s readout := by
  rw [←actual_crossing_source_whole_exterior_history N r left right exterior preops concurrent suffix s
    prefixSeparate concurrentFirst concurrentOthers suffixSeparate middlePure]
  simp only [actualCrossingHistoryRun,actualPhysicalCrossingCompletedHistory,PMF.bind_bind,PMF.bind_map]
  apply bind_eq_of_eq_on_support
  intro first hf
  let p := first.getLastD s
  have hp := real_history_end_support N r preops s first hf
  apply bind_eq_of_eq_on_support
  intro middle hm
  let q := middle.getLastD p
  have hq := real_history_end_support N r concurrent p middle hm
  apply bind_eq_of_eq_on_support
  intro last hl
  let z := last.getLastD q
  have hz := real_history_end_support N r suffix q last hl
  change crossingCompletedTerminal N r left right exterior future s readout
      (crossingMarker N left right exterior s first middle last) = _
  rw [crossingCompletedTerminal,actual_crossing_final_whole_view N left right exterior hpart s first middle last
      (finalPure p hp q hq z hz),actual_completed_terminal_at_source N r future s z
        (rootSupport p hp q hq z hz) readout]
  rfl

#print axioms actual_crossing_history_same_completed_future
end G1CrossingHistorySameActualCompletion
