import G2SourcePairMatrixReadout

/-!
Joint terminal topology read from the actual complete chronological source path.
Contributor: dot (OpenAI), 6 October 2026.
-/
namespace GProgram.G2.CompleteTerminalReadout
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceLiteralClockEndpoint
open GProgram.G2.EventualPathReadout GProgram.G2.CompleteDecoration
open GProgram.G2.CompletedPathProjection GProgram.G2.ChronologicalPathReadout
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.FiniteAncestralTrace
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CalendarPathProjection
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] [Fintype Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.LiteralMarkedClockTrace.choiceOptionMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable

lemma terminal_readout_event_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (f : Code N sample → Q) :
    MeasurableSet {z : CompleteCalendarRecord N sample ops |
      terminalPath (chronologicalPath N ops (observeCompleted N f ops s z)) =
        some (f (completeEnd N ops z))} := by
  have hp := (chronological_path_measurable N ops).comp (observe_completed_measurable N f ops s)
  have ht := terminal_path_measurable.comp hp
  have he := (measurable_of_countable (fun d : Code N sample => some (f d))).comp
    (complete_end_measurable N ops)
  exact measurableSet_eq_fun ht he

/-- Actual topology and pair ages are observed from one complete path. The
terminal value is almost surely its original finite source trace endpoint. -/
theorem actual_terminal_readout (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (s : Code N sample) (f : Code N sample → Q) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s,
      terminalPath (chronologicalPath N ops (observeCompleted N f ops s z)) =
        some (f (completeEnd N ops z)) := by
  rw [completeCalendarTraceLaw,ae_finsetSum_measure_iff]
  intro d _
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have hm := terminal_readout_event_measurable N ops s f
  have hmap : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) := measurable_const.prodMk measurable_id
  apply (ae_map_iff hmap.aemeasurable hm).mpr
  apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
  apply Filter.Eventually.of_forall
  intro past
  rw [completeAncestralTraceLaw]
  have hin : Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) => (d,past,z)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  apply (ae_map_iff (complete_ancestral_trace_measurable N d).aemeasurable (hm.preimage hin)).mpr
  filter_upwards [actual_current_clock_regular_ae N r d] with c hc
  exact actual_completed_chronological_terminal N s d ops past c hc f

#print axioms actual_terminal_readout
end GProgram.G2.CompleteTerminalReadout

/-! Function-level completion-reader normalization for the unchanged faithful
consumer. Contributor: dot (OpenAI), 7 October 2026.
The historical CompleteTerminalReadout body above is an exact prefix.
The old consumer uses `simp only [observeCompleted, completePath, hc.1]`.
This equation has the consumer's current-namespace name, so that explicit
simp list selects the proved equality of whole path functions. It changes
neither the canonical reader nor any completion/event flag or hypothesis.
No reducibility attribute or simplifier option is changed. -/
namespace GProgram.G2.FaithfulTimedOutput
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.EpochHistoryReadout
open scoped NNReal
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [MeasurableSpace Q]

/-- The canonical complete path is the function of the recorded trace alone.
This function-level equation also covers an unapplied path argument. -/
lemma completePath (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (s : Code N sample)
    (z : Bool × ClockTrace N sample (Fintype.card Copy)) :
    CompleteEpochPath.completePath N f s z =
      fun t : ℝ≥0 => f (cutEndpoint N (Fintype.card Copy) (t : ℝ) s z.2) := rfl

#print axioms completePath
end GProgram.G2.FaithfulTimedOutput
