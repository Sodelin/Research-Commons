import G5ObservedEpochConditioning
import G2ActualSegmentPathLaw

/-! Formal use-site of the accepted original-view posterior addendum's CUT
identity. All calendar/clock providers are reused. No new stochastic law is
postulated. The full calendar induction and conditioned germ are separate
consumers of this exact interior-segment identity. -/
namespace GProgram.G5.OriginalInteriorCutLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CalendarPathProjection GProgram.G2.ActualSegmentPathLaw
open GProgram.G2.EpochPathProjection GProgram.G2.EpochHistoryReadout
open GProgram.G2.CompleteAncestralPath
open GProgram.G5.ObservedEpochConditioning
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Read the cut from the original LONG interval record, not a fresh path. -/
theorem actual_interval_cut_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (h t : ℝ≥0) (ht : t < h) :
    (actualSegmentLaw N r (.interval h) s).map
      (fun z => segmentPath N id (.interval h) s z t) =
      (sourceTimeKernel N r t s).toMeasure := by
  let ev : SegmentObservation (Code N sample) → Code N sample := fun z => z.1 t
  have hev : Measurable ev := (measurable_pi_apply t).comp measurable_fst
  have hh := congrArg (fun μ => Measure.map ev μ)
    (actual_interval_observation_law N r id h s)
  rw [Measure.map_map hev (observed_segment_measurable N id (.interval h) s)] at hh
  have hl : ev ∘ observedSegment N id (.interval h) s =
      (fun z => segmentPath N id (.interval h) s z t) := by
    funext z
    exact observed_segment_interior N id h s z t ht
  rw [hl] at hh
  rw [Measure.map_map hev (stopped_path_observation_measurable h),
    Measure.map_map (hev.comp (stopped_path_observation_measurable h))
      (path_projection_measurable measurable_id),
    Measure.map_map ((hev.comp (stopped_path_observation_measurable h)).comp
      (path_projection_measurable measurable_id)) (literal_epoch_path_measurable N s)] at hh
  have hf : ((ev ∘ stoppedPathObservation h) ∘ pathProjection id) ∘ literalEpochPath N s =
      (fun c => literalEpochPath N s c t) := by
    funext c
    simp [ev, stoppedPathObservation, pathProjection, min_eq_left (le_of_lt ht)]
  rw [hf] at hh
  exact hh.trans (actual_epoch_endpoint_law N r s t)

#print axioms actual_interval_cut_law
end GProgram.G5.OriginalInteriorCutLaw
