import G2ChronologicalPathReadout
import G2EpochPathProjection

/-!
Joint observed clamped path and terminal state for one actual source segment.
Contributor: dot (OpenAI), 6 October 2026.

An interval record is read at min(t,h), jointly with its attached endpoint.
Both coordinates are one measurable transform of the same literal clock path.
Boundary records use the original source boundary row. This proves joint
representation independence without inferring it from separate marginals.
Whole-calendar concatenation and age-decoding claims are not made here.
-/
namespace GProgram.G2.ActualSegmentPathLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCrossCarrierProgram
open UnifiedLean.Source.SourceCrossCarrierEpoch UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CalendarPathProjection GProgram.G2.EpochHistoryReadout
open GProgram.G2.CompleteAncestralPath GProgram.G2.EpochPathProjection
open GProgram.G2.SourceFiniteHistory
open scoped Classical NNReal

abbrev SegmentObservation (Q : Type*) := (ℝ≥0 → Q) × Q

/-- One transform preserves the dependence of the stopped path and terminal
coordinate. The full time-indexed function space has its product sigma-algebra. -/
def stoppedPathObservation {Q : Type*} (h : ℝ≥0) (p : ℝ≥0 → Q) :
    SegmentObservation Q := (fun t => p (min t h),p h)

lemma stopped_path_observation_measurable {Q : Type*} [MeasurableSpace Q] (h : ℝ≥0) :
    Measurable (stoppedPathObservation (Q := Q) h) :=
  (measurable_pi_lambda _ (fun t => measurable_pi_apply (min t h))).prodMk
    (measurable_pi_apply h)

def constantObservation {Q : Type*} (q : Q) : SegmentObservation Q := (fun _ => q,q)

lemma constant_observation_measurable {Q : Type*} [MeasurableSpace Q] :
    Measurable (constantObservation (Q := Q)) :=
  (measurable_pi_lambda _ (fun _ => measurable_id)).prodMk measurable_id

variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [MeasurableSpace Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.EpochPathProjection.joinedIndexMeasurable

/-- The stored endpoint remains an independent record field in this definition.
No consistency of arbitrary records is presumed. -/
noncomputable def observedSegment (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (op : ProgramStep N) (s : Code N sample)
    (z : SegmentRecord N sample) : SegmentObservation Q :=
  match op with
  | .interval h => (fun t => segmentPath N f (.interval h) s z (min t h),f z.2)
  | .boundary _ => constantObservation (f z.2)

lemma observed_segment_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (op : ProgramStep N) (s : Code N sample) :
    Measurable (observedSegment N f op s) := by
  cases op with
  | interval h =>
      exact (measurable_pi_lambda _ (fun t =>
        (measurable_pi_apply (min t h)).comp (segment_path_measurable N f (.interval h) s))).prodMk
          ((measurable_of_countable f).comp measurable_snd)
  | boundary b =>
      exact constant_observation_measurable.comp ((measurable_of_countable f).comp measurable_snd)

lemma observed_segment_interior (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (h : ℝ≥0) (s : Code N sample)
    (z : SegmentRecord N sample) (t : ℝ≥0) (ht : t < h) :
    (observedSegment N f (.interval h) s z).1 t = segmentPath N f (.interval h) s z t := by
  simp only [observedSegment,min_eq_left (le_of_lt ht)]

/-- Simultaneous path and terminal readout on each original clock vector,
including h=0 and exceptional compiler records. -/
theorem actual_interval_observation_agrees (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (h : ℝ≥0) (s : Code N sample) (c : Choice N s → ℝ) :
    observedSegment N f (.interval h) s
      (attachEndpoint N s (literalMarkedTrace N (Fintype.card Copy) (h : ℝ) s c)) =
      stoppedPathObservation h (pathProjection f (literalEpochPath N s c)) := by
  apply Prod.ext
  · funext t
    change f (cutEndpoint N (Fintype.card Copy) (min t h : ℝ≥0) s
      (literalMarkedTrace N (Fintype.card Copy) (h : ℝ) s c).2) =
        f (traceEndpoint N (Fintype.card Copy) s
          (literalMarkedTrace N (Fintype.card Copy) (min t h : ℝ≥0) s c).2)
    congr 1
    apply actual_history_cut_readout
    exact_mod_cast (min_le_right t h)
  · rfl

/-- Joint interval-law identity, derived by composing the actual compiler.
The endpoint is the h-coordinate of the SAME path used for clamping. -/
theorem actual_interval_observation_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (f : Code N sample → Q) (h : ℝ≥0) (s : Code N sample) :
    (actualSegmentLaw N r (.interval h) s).map (observedSegment N f (.interval h) s) =
      (((currentPairClockMeasure N r s).map (literalEpochPath N s)).map
        (pathProjection f)).map (stoppedPathObservation h) := by
  have hm := marked_trace_measurable N (Fintype.card Copy) s (h : ℝ)
  have hf : Measurable f := measurable_of_countable f
  rw [actualSegmentLaw,actualMarkedTraceLaw,
    Measure.map_map (attach_endpoint_measurable N s) hm,
    Measure.map_map (observed_segment_measurable N f (.interval h) s)
      ((attach_endpoint_measurable N s).comp hm),
    Measure.map_map (path_projection_measurable hf) (literal_epoch_path_measurable N s),
    Measure.map_map (stopped_path_observation_measurable h)
      ((path_projection_measurable hf).comp (literal_epoch_path_measurable N s))]
  congr 1
  funext c
  exact actual_interval_observation_agrees N f h s c

/-- A boundary contributes a constant observed path with its actual post-step
state as terminal coordinate, under the original boundary kernel. -/
theorem actual_boundary_observation_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (f : Code N sample → Q) (b : BoundaryOperation N)
    (s : Code N sample) :
    (actualSegmentLaw N r (.boundary b) s).map (observedSegment N f (.boundary b) s) =
      (((boundaryKernel N b s).toMeasure).map f).map constantObservation := by
  rw [actualSegmentLaw,
    Measure.map_map (observed_segment_measurable N f (.boundary b) s) (boundary_record_measurable N),
    Measure.map_map constant_observation_measurable (measurable_of_countable f)]
  rfl

/-- Both branches retain their literal segment measure and their original
carrier projection. Only the observation space is shared. -/
noncomputable def joinedObservedSegmentLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N) :
    JoinedCode N sample keep → Measure (SegmentObservation (JoinedIndex N sample keep))
  | .inl s => (actualSegmentLaw N r op s).map
      (observedSegment N (fun d => joinedProjection N keep (.inl d)) op s)
  | .inr s => (actualSegmentLaw N r op s).map
      (observedSegment N (fun d => joinedProjection N keep (.inr d)) op s)

lemma joined_observed_segment_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (s : JoinedCode N sample keep) : IsProbabilityMeasure (joinedObservedSegmentLaw N r keep op s) := by
  cases s with
  | inl s =>
      letI := actual_segment_probability N r op s
      exact Measure.isProbabilityMeasure_map (observed_segment_measurable N _ op s).aemeasurable
  | inr s =>
      letI := actual_segment_probability N r op s
      exact Measure.isProbabilityMeasure_map (observed_segment_measurable N _ op s).aemeasurable

lemma joined_observed_interval_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (h : ℝ≥0) (s : JoinedCode N sample keep) :
    joinedObservedSegmentLaw N r keep (.interval h) s =
      (joinedObservedEpochPathLaw N r keep s).map (stoppedPathObservation h) := by
  cases s with
  | inl s =>
      rw [joinedObservedSegmentLaw,actual_interval_observation_law,
        Measure.map_map (path_projection_measurable measurable_from_top)
          (literal_epoch_path_measurable N s)]
      rfl
  | inr s =>
      rw [joinedObservedSegmentLaw,actual_interval_observation_law,
        Measure.map_map (path_projection_measurable measurable_from_top)
          (literal_epoch_path_measurable N s)]
      rfl

/-- The common boundary row is the original commonProgramStep. No new boundary
rule, projected register, or desired row equality is supplied as a premise. -/
lemma joined_observed_boundary_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (b : BoundaryOperation N)
    (s : JoinedCode N sample keep) :
    joinedObservedSegmentLaw N r keep (.boundary b) s =
      ((commonProgramStep N r keep (.boundary b) (joinedProjection N keep s)).toMeasure).map
        constantObservation := by
  cases s with
  | inl s =>
      rw [joinedObservedSegmentLaw,actual_boundary_observation_law,
        PMF.toMeasure_map _ _ measurable_from_top]
      change (((sourceProgramStep N r (.boundary b) s).map
        (fun d => joinedProjection N keep (.inl d))).toMeasure).map constantObservation = _
      rw [full_source_step_common]
  | inr s =>
      rw [joinedObservedSegmentLaw,actual_boundary_observation_law,
        PMF.toMeasure_map _ _ measurable_from_top]
      change (((sourceProgramStep N r (.boundary b) s).map
        (fun d => joinedProjection N keep (.inr d))).toMeasure).map constantObservation = _
      rw [small_source_step_common]

/-- Equality of the original labelled projection implies equality of the joint
path-terminal measure for all four combinations of full and small carriers. -/
theorem joined_observed_segment_eq (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (s d : JoinedCode N sample keep) (hs : joinedProjection N keep s = joinedProjection N keep d) :
    joinedObservedSegmentLaw N r keep op s = joinedObservedSegmentLaw N r keep op d := by
  cases op with
  | interval h =>
      rw [joined_observed_interval_law,joined_observed_interval_law,
        joined_observed_epoch_path_eq N r keep s d hs]
  | boundary b => rw [joined_observed_boundary_law,joined_observed_boundary_law,hs]

noncomputable def commonObservedSegmentLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (q : JoinedIndex N sample keep) : Measure (SegmentObservation (JoinedIndex N sample keep)) :=
  joinedObservedSegmentLaw N r keep op (joinedRepresentative N keep q)

theorem joined_observed_segment_common (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (s : JoinedCode N sample keep) :
    joinedObservedSegmentLaw N r keep op s =
      commonObservedSegmentLaw N r keep op (joinedProjection N keep s) := by
  apply joined_observed_segment_eq
  exact (Subtype.ext (joinedRepresentative_view N keep (joinedProjection N keep s))).symm

/-- Restricting the JOINT law to a projected terminal fibre preserves the whole
path dependence, including zero-mass fibres. No conditional division occurs. -/
theorem joined_observed_segment_fibre_eq (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (s d : JoinedCode N sample keep) (hs : joinedProjection N keep s = joinedProjection N keep d)
    (q : JoinedIndex N sample keep) :
    (joinedObservedSegmentLaw N r keep op s).restrict {z | z.2 = q} =
      (joinedObservedSegmentLaw N r keep op d).restrict {z | z.2 = q} := by
  rw [joined_observed_segment_eq N r keep op s d hs]

/-- One actual segment, including empty panels with the original register
compatibility still required. This is not a whole-calendar theorem. -/
theorem actual_cross_carrier_segment_path_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N) (s : Code N sample)
    (d : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state d) Finset.univ)) :
    (actualSegmentLaw N r op s).map
      (observedSegment N (fun z => joinedProjection N keep (.inl z)) op s) =
    (actualSegmentLaw N r op d).map
      (observedSegment N (fun z => joinedProjection N keep (.inr z)) op d) :=
  joined_observed_segment_eq N r keep op (.inl s) (.inr d) (Subtype.ext hs)

#print axioms stopped_path_observation_measurable
#print axioms constant_observation_measurable
#print axioms observed_segment_measurable
#print axioms observed_segment_interior
#print axioms actual_interval_observation_agrees
#print axioms actual_interval_observation_law
#print axioms actual_boundary_observation_law
#print axioms joined_observed_segment_probability
#print axioms joined_observed_interval_law
#print axioms joined_observed_boundary_law
#print axioms joined_observed_segment_eq
#print axioms joined_observed_segment_common
#print axioms joined_observed_segment_fibre_eq
#print axioms actual_cross_carrier_segment_path_law
end GProgram.G2.ActualSegmentPathLaw
