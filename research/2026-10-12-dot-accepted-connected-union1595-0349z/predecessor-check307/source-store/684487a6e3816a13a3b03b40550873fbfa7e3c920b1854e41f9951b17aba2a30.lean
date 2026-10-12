import G2CalendarPathProjection

/-!
Joint actual calendar paths and the actual random-cover ancestral tail.
Contributor: dot (OpenAI), 7 October 2026. The finite endpoint-fibre identity
retains the full observed past and tail jointly, including null fibres.
Chronological gluing and faithful timed decoding remain separate.
-/
namespace GProgram.G2.CompletedCalendarPathLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.FiniteAncestralTrace
open GProgram.G2.ActualSegmentPathLaw GProgram.G2.CalendarPathProjection
open GProgram.G2.FiniteFibreTransport GProgram.G2.EpochPathProjection
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [MeasurableSpace Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.EpochPathProjection.joinedIndexMeasurable

abbrev CompletedSegmentObservation (Q : Type*) (n : Nat) :=
  (Fin n → SegmentObservation Q) × (ℝ≥0 → Q)

noncomputable def observedCompleted (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample)
    (z : CompleteCalendarRecord N sample ops) : CompletedSegmentObservation Q ops.length :=
  (observeCalendarSegments N f ops s z.2.1, CompleteEpochPath.completePath N f z.1 z.2.2)

lemma observed_completed_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (observedCompleted N f ops s) := by
  have hm : Measurable (fun z : Code N sample ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) =>
      CompleteEpochPath.completePath N f z.1 z.2) :=
    measurable_from_prod_countable_right (CompleteEpochPath.complete_path_measurable N f)
  exact ((observe_calendar_segments_measurable N f ops s).comp measurable_snd.fst).prodMk
    (hm.comp (measurable_fst.prodMk measurable_snd.snd))

/-- Actual records store the same terminal state used by the ancestral tail. -/
theorem actual_completed_terminal_coherence (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s, z.1 = calendarEnd N ops s z.2.1 := by
  rw [completeCalendarTraceLaw,← Measure.sum_fintype]
  apply Measure.ae_sum_iff.mpr
  intro d
  have hinsert : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) :=
    measurable_const.prodMk measurable_id
  have hA : MeasurableSet {z : Fin ops.length → SegmentRecord N sample |
      calendarEnd N ops s z = d} :=
    measurableSet_eq_fun (calendar_end_measurable N ops s) measurable_const
  have hprod : ∀ᵐ z ∂((actualCalendarTraceLaw N r ops s).restrict
      {z | calendarEnd N ops s z = d}).prod (completeAncestralTraceLaw N r d),
      calendarEnd N ops s z.1 = d := by
    letI := actual_calendar_trace_probability N r ops s
    letI := complete_ancestral_trace_probability N r d
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun ((calendar_end_measurable N ops s).comp measurable_fst)
        measurable_const)).mpr
    filter_upwards [ae_restrict_mem hA] with z hz
    exact Filter.Eventually.of_forall (fun _ => hz)
  exact (ae_map_iff hinsert.aemeasurable
    (measurableSet_eq_fun measurable_fst
      ((calendar_end_measurable N ops s).comp measurable_snd.fst))).mpr
      (hprod.mono (fun _ h => h.symm))

lemma completed_branch_observation_map (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (f : Code N sample → Q)
    (ops : List (ProgramStep N)) (s d : Code N sample) :
    (((((actualCalendarTraceLaw N r ops s).restrict {z | calendarEnd N ops s z = d}).prod
      (completeAncestralTraceLaw N r d)).map (fun z => (d,z))).map
        (observedCompleted N f ops s)) =
      (((actualCalendarTraceLaw N r ops s).restrict {z | calendarEnd N ops s z = d}).map
        (observeCalendarSegments N f ops s)).prod
        ((completeAncestralTraceLaw N r d).map (CompleteEpochPath.completePath N f d)) := by
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have hi : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) :=
    measurable_const.prodMk measurable_id
  rw [Measure.map_map (observed_completed_measurable N f ops s) hi]
  change (((actualCalendarTraceLaw N r ops s).restrict {z | calendarEnd N ops s z = d}).prod
      (completeAncestralTraceLaw N r d)).map
      (Prod.map (observeCalendarSegments N f ops s) (CompleteEpochPath.completePath N f d)) = _
  exact (Measure.map_prod_map _ _ (observe_calendar_segments_measurable N f ops s)
    (CompleteEpochPath.complete_path_measurable N f d)).symm

variable [Fintype Q] [MeasurableSingletonClass Q]

lemma observed_calendar_end_measurable (N : RootedBinary V E X)
    (ops : List (ProgramStep N)) (q : Q) : Measurable (observedCalendarEnd N ops q) := by
  induction ops generalizing q with
  | nil => exact measurable_const
  | cons op ops ih =>
      have hm : Measurable (fun z : Q × (Fin ops.length → SegmentObservation Q) =>
          observedCalendarEnd N ops z.1 z.2) := measurable_from_prod_countable_right ih
      have ht : Measurable (Fin.tail : (Fin (op::ops).length → SegmentObservation Q) →
          (Fin ops.length → SegmentObservation Q)) :=
        measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)
      exact hm.comp (((measurable_pi_apply 0).snd).prodMk ht)

noncomputable def coarseCompletedLaw (N : RootedBinary V E X)
    (K : ProgramStep N → Q → Measure (SegmentObservation Q))
    (T : Q → Measure (ℝ≥0 → Q)) (ops : List (ProgramStep N)) (q : Q) :
    Measure (CompletedSegmentObservation Q ops.length) :=
  ∑ d : Q, ((coarseCalendarLaw N K ops q).restrict
    {z | observedCalendarEnd N ops q z = d}).prod (T d)

/-- Generic transport helper; the actual specialization below derives both
row premises from the original clock laws already proved. -/
theorem actual_completed_common (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (f : Code N sample → Q)
    (K : ProgramStep N → Q → Measure (SegmentObservation Q))
    (T : Q → Measure (ℝ≥0 → Q))
    (hK : ∀ op q, IsProbabilityMeasure (K op q))
    (hT : ∀ q, IsProbabilityMeasure (T q))
    (hrow : ∀ op d, (actualSegmentLaw N r op d).map (observedSegment N f op d) = K op (f d))
    (htail : ∀ d, (completeAncestralTraceLaw N r d).map
      (CompleteEpochPath.completePath N f d) = T (f d))
    (ops : List (ProgramStep N)) (s : Code N sample) :
    (completeCalendarTraceLaw N r ops s).map (observedCompleted N f ops s) =
      coarseCompletedLaw N K T ops (f s) := by
  letI := actual_calendar_trace_probability N r ops s
  letI : ∀ q, IsProbabilityMeasure (T q) := hT
  letI : ∀ q, SFinite (T q) := fun q => inferInstance
  rw [completeCalendarTraceLaw,
    Measure.map_finset_sum' (observed_completed_measurable N f ops s).aemeasurable]
  simp_rw [completed_branch_observation_map,htail]
  have h := finite_endpoint_fibre_product_regroup (actualCalendarTraceLaw N r ops s)
    (calendarEnd N ops s) (observeCalendarSegments N f ops s) f
    (observedCalendarEnd N ops (f s)) (calendar_end_measurable N ops s)
    (observe_calendar_segments_measurable N f ops s)
    (observed_calendar_end_measurable N ops (f s))
    (observe_calendar_terminal_agrees N f ops s) T
  rw [actual_calendar_segments_common N r f K hK hrow] at h
  exact h

noncomputable def commonAncestralPathLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (q : JoinedIndex N sample keep) :
    Measure (ℝ≥0 → JoinedIndex N sample keep) :=
  joinedObservedEpochPathLaw N r keep (joinedRepresentative N keep q)

lemma common_ancestral_path_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (q : JoinedIndex N sample keep) :
    IsProbabilityMeasure (commonAncestralPathLaw N r keep q) :=
  joined_observed_epoch_path_probability N r keep (joinedRepresentative N keep q)

lemma actual_observed_ancestral_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) {S : Type*} [MeasurableSpace S]
    (f : Code N sample → S) (s : Code N sample) :
    (completeAncestralTraceLaw N r s).map (CompleteEpochPath.completePath N f s) =
      (currentPairClockMeasure N r s).map
        (fun c => pathProjection f (CompleteAncestralPath.literalEpochPath N s c)) := by
  change (completeAncestralTraceLaw N r s).map
    (pathProjection f ∘ CompleteAncestralPath.completePath N s) = _
  rw [← Measure.map_map (path_projection_measurable (measurable_of_countable f))
    (CompleteAncestralPath.complete_path_measurable N s),
    CompleteAncestralPath.actual_complete_path_law,
    Measure.map_map (path_projection_measurable (measurable_of_countable f))
      (CompleteAncestralPath.literal_epoch_path_measurable N s)]
  rfl

lemma full_ancestral_path_common (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N sample) :
    (completeAncestralTraceLaw N r s).map
      (CompleteEpochPath.completePath N (fun z => joinedProjection N keep (.inl z)) s) =
      commonAncestralPathLaw N r keep (joinedProjection N keep (.inl s)) := by
  rw [actual_observed_ancestral_law]
  change joinedObservedEpochPathLaw N r keep (.inl s) = _
  apply joined_observed_epoch_path_eq
  exact (Subtype.ext (joinedRepresentative_view N keep (joinedProjection N keep (.inl s)))).symm

lemma small_ancestral_path_common (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N (selectedSample sample keep)) :
    (completeAncestralTraceLaw N r s).map
      (CompleteEpochPath.completePath N (fun z => joinedProjection N keep (.inr z)) s) =
      commonAncestralPathLaw N r keep (joinedProjection N keep (.inr s)) := by
  rw [actual_observed_ancestral_law]
  change joinedObservedEpochPathLaw N r keep (.inr s) = _
  apply joined_observed_epoch_path_eq
  exact (Subtype.ext (joinedRepresentative_view N keep (joinedProjection N keep (.inr s)))).symm

/-- Original full/small laws for the entire calendar observation and actual
ancestral path jointly, with one unchanged register and source programme. -/
theorem actual_cross_carrier_completed_paths (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (d : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state d) Finset.univ)) :
    (completeCalendarTraceLaw N r ops s).map
      (observedCompleted N (fun z => joinedProjection N keep (.inl z)) ops s) =
    (completeCalendarTraceLaw N r ops d).map
      (observedCompleted N (fun z => joinedProjection N keep (.inr z)) ops d) := by
  rw [actual_completed_common N r _ (commonObservedSegmentLaw N r keep)
      (commonAncestralPathLaw N r keep) (common_segment_probability N r keep)
      (common_ancestral_path_probability N r keep)
      (fun op z => joined_observed_segment_common N r keep op (.inl z))
      (full_ancestral_path_common N r keep),
    actual_completed_common N r _ (commonObservedSegmentLaw N r keep)
      (commonAncestralPathLaw N r keep) (common_segment_probability N r keep)
      (common_ancestral_path_probability N r keep)
      (fun op z => joined_observed_segment_common N r keep op (.inr z))
      (small_ancestral_path_common N r keep)]
  have he : joinedProjection N keep (.inl s) = joinedProjection N keep (.inr d) := Subtype.ext hs
  rw [he]

#print axioms observed_completed_measurable
#print axioms actual_completed_terminal_coherence
#print axioms completed_branch_observation_map
#print axioms observed_calendar_end_measurable
#print axioms actual_completed_common
#print axioms common_ancestral_path_probability
#print axioms actual_observed_ancestral_law
#print axioms full_ancestral_path_common
#print axioms small_ancestral_path_common
#print axioms actual_cross_carrier_completed_paths
end GProgram.G2.CompletedCalendarPathLaw
