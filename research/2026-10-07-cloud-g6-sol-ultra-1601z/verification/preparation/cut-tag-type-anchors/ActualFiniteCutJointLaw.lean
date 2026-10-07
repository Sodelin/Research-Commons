import ActualCutJointLaw
import ActualCalendarCutContext

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED separate finite-interval source-law derivative. This consumes the
actual whole-past retained-clock law and original finite continuation. It
does not substitute a completion law at a finite horizon or assume cut
renewal. All existing author bytes and current compiler inputs stay fixed.
-/

namespace CloudG3.ActualFiniteCutJointLaw
set_option backward.isDefEq.respectTransparency false

universe u v w x y

open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceLiteralClockEndpoint UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.LiteralCutResidual
open GProgram.G2.SameClockContinuation GProgram.G2.SameClockPastFutureLaw
open GProgram.G2.HistoryResidualAttachment GProgram.G2.ActualCalendarTrace
open GProgram.G2.CalendarDecoration GProgram.G2.ChronologicalPathReadout
open UnifiedLean.G6.BinFold
open CloudG3.ActualCutTagRefinement CloudG3.ActualCutJointLaw
open CloudG3.ActualTailBinRow CloudG3.ActualCalendarCutContext
open scoped Classical NNReal BigOperators

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.HistoryResidualAttachment.current_clock_probability

noncomputable def cutIntervalReadout (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (s : Code N sample) (offset v : ℝ) :
    (Copy → Copy → Tag) × CutResidual N sample → TaggedEndpoint (Tag := Tag) N sample :=
  fun z => match z.2 with
    | .inl _ => (s, z.1)
    | .inr q => tailTraceReadout N bin q.1 offset z.1
        (literalMarkedTrace N (Fintype.card Copy) v q.1 q.2)

theorem cut_interval_readout_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (offset v : ℝ) :
    Measurable (cutIntervalReadout N bin s offset v) := by
  apply measurable_from_prod_countable_right
  intro B
  have hm : Measurable (fun q : (Σ d : Code N sample, Choice N d → ℝ) =>
      tailTraceReadout N bin q.1 offset B
        (literalMarkedTrace N (Fintype.card Copy) v q.1 q.2)) := by
    intro A hA
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro d
    exact ((tail_trace_readout_measurable N bin hbin d offset B).comp
      (marked_trace_measurable N (Fintype.card Copy) d v)) hA
  exact measurable_const.sumElim hm

theorem same_clock_finite_joint_cut_refinement (N : RootedBinary V E X)
    {sample : Copy → X} (bin : ℝ → Tag) (s d : Code N sample)
    (offset t v : ℝ) (B : Copy → Copy → Tag)
    (c : Choice N s → ℝ) (k : Choice N d → ℝ) (hc : ClockRegular c)
    (ht : 0 ≤ t) (hv : 0 ≤ v)
    (hcut : literalCutResidual N (Fintype.card Copy) t s c = encodeResidual N d k) :
    tailTraceReadout N bin s offset B
        (literalMarkedTrace N (Fintype.card Copy) (t + v) s c) =
      prefixTailReadout N bin s d offset t B
        (literalMarkedTrace N (Fintype.card Copy) t s c,
          literalMarkedTrace N (Fintype.card Copy) v d k) := by
  have hn : liveCard s ≤ Fintype.card Copy := Finset.card_le_univ s.val.live
  have hk := residual_regular_and_card N (Fintype.card Copy) t s d c k hc hcut
  have he := same_clock_endpoint_continuation N (Fintype.card Copy) t v s d c k
    hc hn ht hv hcut
  rw [← marked_trace_endpoint_eq N (Fintype.card Copy) s (t + v) c,
    ← marked_trace_endpoint_eq N (Fintype.card Copy) d v k] at he
  have hleft := marked_trace_success_on_regular N (Fintype.card Copy) s (t + v) c hn hc
  have hright := marked_trace_success_on_regular N (Fintype.card Copy) d v k
    (le_trans hk.1 hn) hk.2
  simp only [decodedEndpoint, hleft, hright, if_true] at he
  apply Prod.ext
  · exact Option.some.inj he
  · exact same_clock_tag_cut_refinement N bin (Fintype.card Copy) t v offset
      s d c k B hc hn ht hv hcut

/-- Interior-cut joint law: whole recorded past and its genuine residual
clocks, at fixed nonnegative durations. No endpoint-only renewal is expanded. -/
theorem interval_cut_fibre_joint_source_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (bin : ℝ → Tag) (hbin : Measurable bin) (offset : ℝ)
    (t v : ℝ≥0) (B : Copy → Copy → Tag) :
    (actualMarkedTraceLaw N r (Fintype.card Copy) s ((t : ℝ) + (v : ℝ))).map
        (tailTraceReadout N bin s offset B) =
      ∑ d : Code N sample,
        ((((actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
          {h | decodedEndpoint N (Fintype.card Copy) s h = some d}).prod
          (actualMarkedTraceLaw N r (Fintype.card Copy) d (v : ℝ))).map
            (prefixTailReadout N bin s d offset (t : ℝ) B)) := by
  let F : (Bool × ClockTrace N sample (Fintype.card Copy)) × CutResidual N sample →
      TaggedEndpoint (Tag := Tag) N sample := fun z => cutIntervalReadout N bin s
        (offset + (t : ℝ)) (v : ℝ)
        (foldTags N bin (Fintype.card Copy) s offset B z.1.2, z.2)
  have hF : Measurable F := (cut_interval_readout_measurable N bin hbin s _ _).comp
    (((fold_tags_joint_measurable N bin hbin (Fintype.card Copy) offset).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_fst.snd))).prodMk measurable_snd)
  have hJ := (marked_trace_measurable N (Fintype.card Copy) s (t : ℝ)).prodMk
    (literal_cut_measurable N (Fintype.card Copy) s (t : ℝ))
  calc
    _ = (actualCutJointLaw N r (Fintype.card Copy) s (t : ℝ)).map F := by
      rw [actualMarkedTraceLaw,
        Measure.map_map (tail_trace_readout_measurable N bin hbin s offset B)
          (marked_trace_measurable N (Fintype.card Copy) s ((t : ℝ) + (v : ℝ))),
        actualCutJointLaw, Measure.map_map hF hJ]
      apply Measure.map_congr
      filter_upwards [actual_current_clock_regular_ae N r s] with c hc
      obtain ⟨d, k, hcut⟩ := actual_cut_residual_success N (Fintype.card Copy)
        (t : ℝ) s c hc (Finset.card_le_univ s.val.live)
      dsimp only [Function.comp_def, F]
      rw [hcut]
      exact same_clock_finite_joint_cut_refinement N bin s d offset t v B c k
        hc t.coe_nonneg v.coe_nonneg hcut
    _ = _ := by
      rw [actual_full_past_terminal_fibres N r (Fintype.card Copy) s t
        (Finset.card_le_univ s.val.live), Measure.map_finset_sum' hF.aemeasurable]
      apply Finset.sum_congr rfl
      intro d _
      let P := (actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
        {h | decodedEndpoint N (Fintype.card Copy) s h = some d}
      letI := actual_marked_trace_probability N r (Fintype.card Copy) s t
      have he : Measurable (fun z : (Bool × ClockTrace N sample (Fintype.card Copy)) ×
          (Choice N d → ℝ) => (z.1, encodeResidual N d z.2)) :=
        measurable_fst.prodMk ((encode_residual_measurable N d).comp measurable_snd)
      have hg := prefix_tail_readout_measurable N bin hbin s d offset (t : ℝ) B
      have hprod : P.prod ((currentPairClockMeasure N r d).map
          (literalMarkedTrace N (Fintype.card Copy) (v : ℝ) d)) =
          (P.prod (currentPairClockMeasure N r d)).map
            (Prod.map id (literalMarkedTrace N (Fintype.card Copy) (v : ℝ) d)) := by
        simpa only [Measure.map_id] using
          Measure.map_prod_map P (currentPairClockMeasure N r d) measurable_id
            (marked_trace_measurable N (Fintype.card Copy) d (v : ℝ))
      rw [Measure.map_map hF he, actualMarkedTraceLaw, hprod,
        Measure.map_map hg
          (measurable_id.prodMap (marked_trace_measurable N (Fintype.card Copy) d (v : ℝ)))]
      rfl

theorem interval_segment_joint_toMeasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (offset : ℝ) (t : ℝ≥0) (B : Copy → Copy → Tag) :
    (segmentJoint N r bin hbin (.interval t) s offset B).toMeasure =
      (actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).map
        (tailTraceReadout N bin s offset B) := by
  rw [segment_joint_toMeasure, actualSegmentLaw,
    Measure.map_map (segment_readout_measurable N bin hbin (.interval t) s offset B)
      (attach_endpoint_measurable N s)]
  rfl

theorem interval_joint_cut_bind (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (offset : ℝ) (t v : ℝ≥0) (B : Copy → Copy → Tag) :
    segmentJoint N r bin hbin (.interval (t + v)) s offset B =
      (segmentJoint N r bin hbin (.interval t) s offset B).bind (fun q =>
        segmentJoint N r bin hbin (.interval v) q.1 (offset + (t : ℝ)) q.2) := by
  letI := actual_marked_trace_probability N r (Fintype.card Copy) s t
  letI : ∀ d : Code N sample,
      IsProbabilityMeasure (actualMarkedTraceLaw N r (Fintype.card Copy) d (v : ℝ)) :=
    fun d => actual_marked_trace_probability N r (Fintype.card Copy) d v
  let g : TaggedEndpoint (Tag := Tag) N sample × (Bool × ClockTrace N sample (Fintype.card Copy)) →
      TaggedEndpoint (Tag := Tag) N sample := fun z => tailTraceReadout N bin z.1.1
        (offset + (t : ℝ)) z.1.2 z.2
  have hg : Measurable g := measurable_from_prod_countable_right (fun q =>
    tail_trace_readout_measurable N bin hbin q.1 (offset + (t : ℝ)) q.2)
  apply PMF.toMeasure_injective
  rw [interval_segment_joint_toMeasure, NNReal.coe_add,
    interval_cut_fibre_joint_source_law N r s bin hbin offset t v B]
  simp_rw [decoded_raw_endpoint_restrict]
  exact finite_observed_fibre_kernel (actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ))
    (fun h => traceEndpoint N (Fintype.card Copy) s h.2)
    (tailTraceReadout N bin s offset B) Prod.fst
    (raw_tail_endpoint_measurable N s) (tail_trace_readout_measurable N bin hbin s offset B)
    measurable_fst (fun _ => rfl)
    (fun d => actualMarkedTraceLaw N r (Fintype.card Copy) d (v : ℝ))
    (segmentJoint N r bin hbin (.interval t) s offset B)
    (interval_segment_joint_toMeasure N r bin hbin s offset t B).symm g hg
    (fun q => segmentJoint N r bin hbin (.interval v) q.1 (offset + (t : ℝ)) q.2)
    (fun q => interval_segment_joint_toMeasure N r bin hbin q.1 (offset + (t : ℝ)) v q.2)

theorem calendar_joint_interval_refinement (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (t v : ℝ≥0) (B : Copy → Copy → Tag) :
    calendarJoint N r bin hbin (.interval (t + v) :: ops) s offset B =
      calendarJoint N r bin hbin (.interval t :: .interval v :: ops) s offset B := by
  rw [calendar_joint_cons, interval_joint_cut_bind, PMF.bind_bind,
    calendar_joint_cons]
  apply congrArg (PMF.bind (segmentJoint N r bin hbin (.interval t) s offset B))
  funext q
  rw [calendar_joint_cons]
  apply congrArg (PMF.bind (segmentJoint N r bin hbin (.interval v)
    q.1 (offset + (t : ℝ)) q.2))
  funext e
  simp only [segmentOffset, NNReal.coe_add, add_assoc]

/-- Any unchanged original prefix may surround the interval refinement.
All its boundary operations and old tag correlation remain in the same bind. -/
theorem calendar_joint_refinement_in_context (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (prefix ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (t v : ℝ≥0) (B : Copy → Copy → Tag) :
    calendarJoint N r bin hbin (prefix ++ .interval (t + v) :: ops) s offset B =
      calendarJoint N r bin hbin (prefix ++ .interval t :: .interval v :: ops) s offset B := by
  rw [calendar_joint_append, calendar_joint_append]
  apply congrArg (PMF.bind (calendarJoint N r bin hbin prefix s offset B))
  funext q
  exact calendar_joint_interval_refinement N r bin hbin ops q.1
    (offset + (programDuration N prefix : ℝ)) t v q.2

#print axioms cut_interval_readout_measurable
#print axioms same_clock_finite_joint_cut_refinement
#print axioms interval_cut_fibre_joint_source_law
#print axioms interval_segment_joint_toMeasure
#print axioms interval_joint_cut_bind
#print axioms calendar_joint_interval_refinement
#print axioms calendar_joint_refinement_in_context

end CloudG3.ActualFiniteCutJointLaw
