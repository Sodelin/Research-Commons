import G2CompletedCalendarPathLaw
import G2ChronologicalGluing

/-!
Actual chronological all-time path law for the complete source calendar.
Contributor: dot (OpenAI), 7 October 2026. Fixed-calendar gluing is applied to
the proved joint calendar/ancestral law. The stored-terminal coherence used
by that gluing is derived on the actual measure. Faithful event-age decoding
and the final decorated endpoint remain separate.
-/
namespace GProgram.G2.ActualChronologicalPathLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CalendarPathProjection
open GProgram.G2.CompletedCalendarPathLaw GProgram.G2.ChronologicalGluing
open GProgram.G2.ChronologicalPathReadout GProgram.G2.EpochPathProjection
open scoped Classical NNReal
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [MeasurableSpace Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.EpochPathProjection.joinedIndexMeasurable

/-- Literal chronological readout, using the actual calendar's computed
terminal state for the attached finite random-cover record. -/
noncomputable def actualChronologicalPath (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample)
    (z : CompleteCalendarRecord N sample ops) : ℝ≥0 → Q :=
  fun t => f (recordPath N ops s z.2.1 z.2.2 t)

lemma actual_chronological_path_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (actualChronologicalPath N f ops s) := by
  have hm : Measurable (fun z : Code N sample ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) =>
      CompleteEpochPath.completePath N f z.1 z.2) :=
    measurable_from_prod_countable_right (CompleteEpochPath.complete_path_measurable N f)
  have ht : Measurable (fun z : CompleteCalendarRecord N sample ops =>
      CompleteEpochPath.completePath N f (calendarEnd N ops s z.2.1) z.2.2) :=
    hm.comp (((calendar_end_measurable N ops s).comp measurable_snd.fst).prodMk
      measurable_snd.snd)
  have hg := (joined_chronological_path_measurable N (Q := Q) ops).comp
    (((observe_calendar_segments_measurable N f ops s).comp measurable_snd.fst).prodMk ht)
  convert hg using 1
  funext z
  exact (joined_record_path_agrees N f ops s z.2.1 z.2.2).symm

/-- The separately stored final state agrees with the computed state on the
actual completed measure, so one measurable gluing reads its full path. -/
theorem actual_chronological_path_join_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (f : Code N sample → Q)
    (ops : List (ProgramStep N)) (s : Code N sample) :
    (completeCalendarTraceLaw N r ops s).map (actualChronologicalPath N f ops s) =
      ((completeCalendarTraceLaw N r ops s).map (observedCompleted N f ops s)).map
        (joinedChronologicalPath N ops) := by
  rw [Measure.map_map (joined_chronological_path_measurable N ops)
    (observed_completed_measurable N f ops s)]
  apply Measure.map_congr
  filter_upwards [actual_completed_terminal_coherence N r ops s] with z hz
  exact (coherent_completed_record_agrees N f ops s z hz).symm

lemma actual_chronological_path_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (f : Code N sample → Q)
    (ops : List (ProgramStep N)) (s : Code N sample) :
    IsProbabilityMeasure ((completeCalendarTraceLaw N r ops s).map
      (actualChronologicalPath N f ops s)) := by
  letI := complete_calendar_trace_probability N r ops s
  exact Measure.isProbabilityMeasure_map (actual_chronological_path_measurable N f ops s).aemeasurable

/-- Full and selected carriers have the same law on the entire chronological
nonnegative-time product path space for every common original programme. -/
theorem actual_cross_carrier_chronological_path_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N sample)
    (d : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state d) Finset.univ)) :
    (completeCalendarTraceLaw N r ops s).map
      (actualChronologicalPath N (fun z => joinedProjection N keep (.inl z)) ops s) =
    (completeCalendarTraceLaw N r ops d).map
      (actualChronologicalPath N (fun z => joinedProjection N keep (.inr z)) ops d) := by
  rw [actual_chronological_path_join_law,actual_chronological_path_join_law,
    actual_cross_carrier_completed_paths N r keep ops s d hs]

#print axioms actual_chronological_path_measurable
#print axioms actual_chronological_path_join_law
#print axioms actual_chronological_path_probability
#print axioms actual_cross_carrier_chronological_path_law
end GProgram.G2.ActualChronologicalPathLaw
