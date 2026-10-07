import ActualCutJointLaw
import CompleteCalendarJointLaw

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED separate actual calendar-context derivative. All finite joint PMFs
below are converted from actual measurable probability pushforwards. Their
bind/append laws are proved from original unnormalized segment/calendar
fibres; no desired calendar, renewal or refinement law is a premise.
No compiler or provider edit ran in this lane. Original author files fixed.
-/

namespace CloudG3.ActualCalendarCutContext
set_option backward.isDefEq.respectTransparency false

universe u v w x y

open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.LiteralCutResidual GProgram.G2.FiniteAncestralTrace
open GProgram.G2.CalendarDecoration GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.CompleteDecoration GProgram.G2.ChronologicalPathReadout
open GProgram.G2.FiniteFibreTransport
open UnifiedLean.G6.BinFold
open CloudG3.ActualCutJointLaw CloudG3.ActualTailBinRow
open CloudG3.CompleteCalendarBinReadout
open scoped Classical NNReal ENNReal BigOperators

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.HistoryResidualAttachment.current_clock_probability

noncomputable def segmentReadout (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (op : ProgramStep N) (s : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) (z : SegmentRecord N sample) : TaggedEndpoint N sample :=
  (z.2, segmentTags N bin op s offset B z)

noncomputable def calendarReadout (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) (z : Fin ops.length → SegmentRecord N sample) :
    TaggedEndpoint N sample :=
  (calendarEnd N ops s z, calendarTags N bin ops s offset B z)

noncomputable def completeReadout (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) (z : CompleteCalendarRecord N sample ops) :
    TaggedEndpoint N sample := (completeEnd N ops z, completeTags N bin ops s offset B z)

theorem segment_readout_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (hbin : Measurable bin) (op : ProgramStep N)
    (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    Measurable (segmentReadout N bin op s offset B) := by
  apply measurable_snd.prodMk
  cases op with
  | interval t =>
      exact (fold_tags_joint_measurable N bin hbin (Fintype.card Copy) offset).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_fst.snd))
  | boundary b => exact measurable_const

theorem calendar_readout_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    Measurable (calendarReadout N bin ops s offset B) := by
  induction ops generalizing s offset B with
  | nil => exact measurable_const
  | cons op ops ih =>
      have hw : Measurable (fun z : TaggedEndpoint N sample ×
          (Fin ops.length → SegmentRecord N sample) =>
          calendarReadout N bin ops z.1.1 (segmentOffset N op offset) z.1.2 z.2) :=
        measurable_from_prod_countable_right (fun q =>
          ih q.1 (segmentOffset N op offset) q.2)
      have ht : Measurable (Fin.tail : (Fin (op :: ops).length → SegmentRecord N sample) →
          (Fin ops.length → SegmentRecord N sample)) := by
        apply measurable_pi_lambda
        intro i
        exact measurable_pi_apply i.succ
      exact hw.comp (((segment_readout_measurable N bin hbin op s offset B).comp
        (measurable_pi_apply 0)).prodMk ht)

theorem complete_readout_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    Measurable (completeReadout N bin ops s offset B) := by
  have hw : Measurable (fun z : TaggedEndpoint N sample ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) =>
      tailTraceReadout N bin z.1.1 (offset + (programDuration N ops : ℝ)) z.1.2 z.2) :=
    measurable_from_prod_countable_right (fun q => tail_trace_readout_measurable N bin hbin
      q.1 (offset + (programDuration N ops : ℝ)) q.2)
  exact hw.comp ((measurable_fst.prodMk
    (((calendar_readout_measurable N bin hbin ops s offset B).comp measurable_snd.fst).snd)).prodMk
      measurable_snd.snd)

noncomputable def segmentJoint (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    PMF (TaggedEndpoint N sample) := by
  letI := actual_segment_probability N r op s
  letI := Measure.isProbabilityMeasure_map
    (segment_readout_measurable N bin hbin op s offset B).aemeasurable
  exact ((actualSegmentLaw N r op s).map (segmentReadout N bin op s offset B)).toPMF

noncomputable def calendarJoint (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    PMF (TaggedEndpoint N sample) := by
  letI := actual_calendar_trace_probability N r ops s
  letI := Measure.isProbabilityMeasure_map
    (calendar_readout_measurable N bin hbin ops s offset B).aemeasurable
  exact ((actualCalendarTraceLaw N r ops s).map (calendarReadout N bin ops s offset B)).toPMF

noncomputable def completedJoint (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    PMF (TaggedEndpoint N sample) := by
  letI := complete_calendar_trace_probability N r ops s
  letI := Measure.isProbabilityMeasure_map
    (complete_readout_measurable N bin hbin ops s offset B).aemeasurable
  exact ((completeCalendarTraceLaw N r ops s).map (completeReadout N bin ops s offset B)).toPMF

noncomputable def tailJoint (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    PMF (TaggedEndpoint N sample) := by
  letI := complete_ancestral_trace_probability N r s
  letI := Measure.isProbabilityMeasure_map
    (tail_trace_readout_measurable N bin hbin s offset B).aemeasurable
  exact ((completeAncestralTraceLaw N r s).map (tailTraceReadout N bin s offset B)).toPMF

theorem segment_joint_toMeasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    (segmentJoint N r bin hbin op s offset B).toMeasure =
      (actualSegmentLaw N r op s).map (segmentReadout N bin op s offset B) := by
  unfold segmentJoint
  exact Measure.toPMF_toMeasure _

theorem calendar_joint_toMeasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    (calendarJoint N r bin hbin ops s offset B).toMeasure =
      (actualCalendarTraceLaw N r ops s).map (calendarReadout N bin ops s offset B) := by
  unfold calendarJoint
  exact Measure.toPMF_toMeasure _

theorem completed_joint_toMeasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    (completedJoint N r bin hbin ops s offset B).toMeasure =
      (completeCalendarTraceLaw N r ops s).map (completeReadout N bin ops s offset B) := by
  unfold completedJoint
  exact Measure.toPMF_toMeasure _

theorem tail_joint_toMeasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    (tailJoint N r bin hbin s offset B).toMeasure =
      (completeAncestralTraceLaw N r s).map (tailTraceReadout N bin s offset B) := by
  unfold tailJoint
  exact Measure.toPMF_toMeasure _

/-- Standard finite measure algebra. In the source applications Gamma and
each row are defined from actual probability pushforwards; hGamma/hrow are
proved toPMF conversion identities, not physical source-law assumptions. -/
theorem finite_observed_fibre_kernel {A S O β R : Type*}
    [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace O]
    [MeasurableSpace β] [MeasurableSpace R]
    [Fintype S] [Fintype O] [Fintype R]
    [MeasurableSingletonClass S] [MeasurableSingletonClass O] [MeasurableSingletonClass R]
    (μ : Measure A) [IsFiniteMeasure μ] (e : A → S) (obs : A → O) (k : O → S)
    (he : Measurable e) (ho : Measurable obs) (hk : Measurable k)
    (hcompat : ∀ a, k (obs a) = e a) (ν : S → Measure β) [∀ s, SFinite (ν s)]
    (Gamma : PMF O) (hGamma : μ.map obs = Gamma.toMeasure)
    (g : O × β → R) (hg : Measurable g) (row : O → PMF R)
    (hrow : ∀ q, (row q).toMeasure = (ν (k q)).map (fun z => g (q, z))) :
    (∑ s : S, ((μ.restrict {a | e a = s}).prod (ν s)).map
      (fun z => g (obs z.1, z.2))) = (Gamma.bind row).toMeasure := by
  have hG := hg.comp (ho.prodMap measurable_id)
  have hfirst : (∑ s : S, ((μ.restrict {a | e a = s}).prod (ν s)).map
      (fun z => g (obs z.1, z.2))) =
      ∑ s : S, (((μ.restrict {a | e a = s}).map obs).prod (ν s)).map g := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← Measure.map_prod_map (μ.restrict {a | e a = s}) (ν s) ho measurable_id,
      Measure.map_id, Measure.map_map hg (ho.prodMap measurable_id)]
    rfl
  have hcoarse := finite_endpoint_fibre_product_regroup_map μ e obs id k
    he ho hk hcompat ν Gamma.toMeasure hGamma g hg
  have hfine := finite_endpoint_fibre_product_regroup_map Gamma.toMeasure id id k k
    measurable_id measurable_id hk (fun _ => rfl) ν Gamma.toMeasure Measure.map_id g hg
  have hpoint (q : O) :
      ((Gamma.toMeasure.restrict {x | x = q}).prod (ν (k q))).map g =
        Gamma q • (row q).toMeasure := by
    rw [CloudG3.CompleteCalendarJointLaw.pmf_singleton_restrict,
      Measure.prod_smul_left, Measure.map_smul, Measure.dirac_prod,
      Measure.map_map hg measurable_prodMk_left, ← hrow q]
  calc
    _ = ∑ s : S, (((μ.restrict {a | e a = s}).map obs).prod (ν s)).map g := hfirst
    _ = ∑ s : S, ((Gamma.toMeasure.restrict {q | k q = s}).prod (ν s)).map g :=
      by simpa only [id_eq] using hcoarse
    _ = ∑ q : O, ((Gamma.toMeasure.restrict {x | x = q}).prod (ν (k q))).map g :=
      by simpa only [id_eq, Measure.map_id] using hfine.symm
    _ = ∑ q : O, Gamma q • (row q).toMeasure := Finset.sum_congr rfl (fun q _ => hpoint q)
    _ = _ := by
      apply Measure.ext
      intro U hU
      rw [Measure.finsetSum_apply, PMF.toMeasure_bind_apply _ _ _ hU, tsum_fintype]
      simp only [Measure.smul_apply, smul_eq_mul]

/-- Cons induction through the ACTUAL original unnormalized segment fibres. -/
theorem calendar_joint_cons (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (op : ProgramStep N) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (B : Copy → Copy → Tag) :
    calendarJoint N r bin hbin (op :: ops) s offset B =
      (segmentJoint N r bin hbin op s offset B).bind (fun q =>
        calendarJoint N r bin hbin ops q.1 (segmentOffset N op offset) q.2) := by
  letI := actual_segment_probability N r op s
  letI : ∀ d : Code N sample, IsProbabilityMeasure (actualCalendarTraceLaw N r ops d) :=
    fun d => actual_calendar_trace_probability N r ops d
  let g : TaggedEndpoint N sample × (Fin ops.length → SegmentRecord N sample) →
      TaggedEndpoint N sample := fun z => calendarReadout N bin ops z.1.1
        (segmentOffset N op offset) z.1.2 z.2
  have hg : Measurable g := measurable_from_prod_countable_right (fun q =>
    calendar_readout_measurable N bin hbin ops q.1 (segmentOffset N op offset) q.2)
  apply PMF.toMeasure_injective
  rw [calendar_joint_toMeasure, actualCalendarTraceLaw,
    Measure.map_finset_sum' (calendar_readout_measurable N bin hbin (op :: ops) s offset B).aemeasurable]
  have hleft : (∑ d : Code N sample,
      ((((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
        (actualCalendarTraceLaw N r ops d)).map (recordCons N ops.length)).map
          (calendarReadout N bin (op :: ops) s offset B)) =
      ∑ d : Code N sample,
        (((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
          (actualCalendarTraceLaw N r ops d)).map
            (fun z => g (segmentReadout N bin op s offset B z.1, z.2)) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [Measure.map_map (calendar_readout_measurable N bin hbin (op :: ops) s offset B)
      (record_cons_measurable N ops.length)]
    rfl
  rw [hleft]
  exact finite_observed_fibre_kernel (actualSegmentLaw N r op s) Prod.snd
    (segmentReadout N bin op s offset B) Prod.fst measurable_snd
    (segment_readout_measurable N bin hbin op s offset B) measurable_fst (fun _ => rfl)
    (fun d => actualCalendarTraceLaw N r ops d)
    (segmentJoint N r bin hbin op s offset B)
    (segment_joint_toMeasure N r bin hbin op s offset B).symm g hg
    (fun q => calendarJoint N r bin hbin ops q.1 (segmentOffset N op offset) q.2)
    (fun q => calendar_joint_toMeasure N r bin hbin ops q.1 (segmentOffset N op offset) q.2)

/-- The entire actual calendar past and its same tags feed the actual tail
row. Compatibility is derived on the original terminal restriction. -/
theorem completed_joint_bind_calendar (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) :
    completedJoint N r bin hbin ops s offset B =
      (calendarJoint N r bin hbin ops s offset B).bind (fun q =>
        tailJoint N r bin hbin q.1 (offset + (programDuration N ops : ℝ)) q.2) := by
  letI := actual_calendar_trace_probability N r ops s
  letI : ∀ d : Code N sample, IsProbabilityMeasure (completeAncestralTraceLaw N r d) :=
    fun d => complete_ancestral_trace_probability N r d
  let g : TaggedEndpoint N sample × (Bool × ClockTrace N sample (Fintype.card Copy)) →
      TaggedEndpoint N sample := fun z => tailTraceReadout N bin z.1.1
        (offset + (programDuration N ops : ℝ)) z.1.2 z.2
  have hg : Measurable g := measurable_from_prod_countable_right (fun q =>
    tail_trace_readout_measurable N bin hbin q.1 (offset + (programDuration N ops : ℝ)) q.2)
  apply PMF.toMeasure_injective
  rw [completed_joint_toMeasure, completeCalendarTraceLaw,
    Measure.map_finset_sum' (complete_readout_measurable N bin hbin ops s offset B).aemeasurable]
  have hleft : (∑ d : Code N sample,
      (((((actualCalendarTraceLaw N r ops s).restrict {p | calendarEnd N ops s p = d}).prod
        (completeAncestralTraceLaw N r d)).map (fun z => (d, z))).map
          (completeReadout N bin ops s offset B))) =
      ∑ d : Code N sample,
        (((actualCalendarTraceLaw N r ops s).restrict {p | calendarEnd N ops s p = d}).prod
          (completeAncestralTraceLaw N r d)).map
            (fun z => g (calendarReadout N bin ops s offset B z.1, z.2)) := by
    apply Finset.sum_congr rfl
    intro d _
    have hinsert : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
        (Bool × ClockTrace N sample (Fintype.card Copy)) => (d, z)) :=
      measurable_const.prodMk measurable_id
    rw [Measure.map_map (complete_readout_measurable N bin hbin ops s offset B) hinsert]
    have hf := (complete_readout_measurable N bin hbin ops s offset B).comp hinsert
    have hr := hg.comp ((calendar_readout_measurable N bin hbin ops s offset B).prodMap measurable_id)
    apply Measure.map_congr
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hf hr)).mpr
    filter_upwards [ae_restrict_mem (measurableSet_eq_fun
      (calendar_end_measurable N ops s) measurable_const)] with past hp
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only [g, Function.comp_def, completeReadout, completeTags, completeEnd,
        calendarReadout, tailTraceReadout]
      rw [hp])
  rw [hleft]
  exact finite_observed_fibre_kernel (actualCalendarTraceLaw N r ops s)
    (calendarEnd N ops s) (calendarReadout N bin ops s offset B) Prod.fst
    (calendar_end_measurable N ops s) (calendar_readout_measurable N bin hbin ops s offset B)
    measurable_fst (fun _ => rfl) (fun d => completeAncestralTraceLaw N r d)
    (calendarJoint N r bin hbin ops s offset B)
    (calendar_joint_toMeasure N r bin hbin ops s offset B).symm g hg
    (fun q => tailJoint N r bin hbin q.1 (offset + (programDuration N ops : ℝ)) q.2)
    (fun q => tail_joint_toMeasure N r bin hbin q.1 (offset + (programDuration N ops : ℝ)) q.2)

/-- The concrete Eq(10) source proof gives the finite joint cut kernel. -/
theorem tail_joint_cut_bind (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (offset : ℝ) (t : ℝ≥0) (B : Copy → Copy → Tag) :
    tailJoint N r bin hbin s offset B =
      (segmentJoint N r bin hbin (.interval t) s offset B).bind (fun q =>
        tailJoint N r bin hbin q.1 (offset + (t : ℝ)) q.2) := by
  letI := actual_marked_trace_probability N r (Fintype.card Copy) s t
  letI : ∀ d : Code N sample, IsProbabilityMeasure (completeAncestralTraceLaw N r d) :=
    fun d => complete_ancestral_trace_probability N r d
  let g : TaggedEndpoint N sample × (Bool × ClockTrace N sample (Fintype.card Copy)) →
      TaggedEndpoint N sample := fun z => tailTraceReadout N bin z.1.1
        (offset + (t : ℝ)) z.1.2 z.2
  have hg : Measurable g := measurable_from_prod_countable_right (fun q =>
    tail_trace_readout_measurable N bin hbin q.1 (offset + (t : ℝ)) q.2)
  have hGamma : (actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).map
      (tailTraceReadout N bin s offset B) =
      (segmentJoint N r bin hbin (.interval t) s offset B).toMeasure := by
    rw [segment_joint_toMeasure, actualSegmentLaw,
      Measure.map_map (segment_readout_measurable N bin hbin (.interval t) s offset B)
        (attach_endpoint_measurable N s)]
    rfl
  apply PMF.toMeasure_injective
  rw [tail_joint_toMeasure, complete_cut_fibre_joint_source_law N r s bin hbin offset t B]
  simp_rw [decoded_raw_endpoint_restrict]
  exact finite_observed_fibre_kernel (actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ))
    (fun h => traceEndpoint N (Fintype.card Copy) s h.2)
    (tailTraceReadout N bin s offset B) Prod.fst
    (raw_tail_endpoint_measurable N s) (tail_trace_readout_measurable N bin hbin s offset B)
    measurable_fst (fun _ => rfl) (fun d => completeAncestralTraceLaw N r d)
    (segmentJoint N r bin hbin (.interval t) s offset B) hGamma g hg
    (fun q => tailJoint N r bin hbin q.1 (offset + (t : ℝ)) q.2)
    (fun q => tail_joint_toMeasure N r bin hbin q.1 (offset + (t : ℝ)) q.2)

theorem calendar_joint_nil (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    calendarJoint N r bin hbin [] s offset B = PMF.pure (s, B) := by
  apply PMF.toMeasure_injective
  rw [calendar_joint_toMeasure]
  simp [actualCalendarTraceLaw, calendarReadout, calendarEnd, calendarTags]

theorem program_duration_append (N : RootedBinary V E X)
    (ops more : List (ProgramStep N)) :
    programDuration N (ops ++ more) = programDuration N ops + programDuration N more := by
  induction ops with
  | nil => simp [programDuration]
  | cons op ops ih => cases op <;> simp [programDuration, ih, add_assoc]

/-- Append preserves each original head operation and its carried joint state. -/
theorem calendar_joint_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops more : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) :
    calendarJoint N r bin hbin (ops ++ more) s offset B =
      (calendarJoint N r bin hbin ops s offset B).bind (fun q =>
        calendarJoint N r bin hbin more q.1 (offset + (programDuration N ops : ℝ)) q.2) := by
  induction ops generalizing s offset B with
  | nil => simp [calendar_joint_nil, programDuration]
  | cons op ops ih =>
      rw [List.cons_append, calendar_joint_cons, ih, calendar_joint_cons, PMF.bind_bind]
      apply congrArg (PMF.bind (segmentJoint N r bin hbin op s offset B))
      funext q
      cases op <;> simp only [segmentOffset, programDuration, NNReal.coe_add, add_assoc]

theorem calendar_joint_single (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag) :
    calendarJoint N r bin hbin [op] s offset B = segmentJoint N r bin hbin op s offset B := by
  rw [calendar_joint_cons]
  simp_rw [calendar_joint_nil]
  exact PMF.bind_pure _

/-- Eq(11) as an ACTUAL complete-calendar measure equality. The source bank,
head boundaries and carried old tags remain original. Ancestral support is
needed for terminal biological semantics, not this defined record equality. -/
theorem actual_complete_calendar_cut_refinement (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (t : ℝ≥0) (B : Copy → Copy → Tag) :
    (completeCalendarTraceLaw N r ops s).map (completeReadout N bin ops s offset B) =
      (completeCalendarTraceLaw N r (ops ++ [.interval t]) s).map
        (completeReadout N bin (ops ++ [.interval t]) s offset B) := by
  rw [← completed_joint_toMeasure, ← completed_joint_toMeasure]
  apply congrArg PMF.toMeasure
  rw [completed_joint_bind_calendar, completed_joint_bind_calendar,
    calendar_joint_append, PMF.bind_bind]
  apply congrArg (PMF.bind (calendarJoint N r bin hbin ops s offset B))
  funext q
  rw [calendar_joint_single]
  rw [tail_joint_cut_bind N r bin hbin q.1 (offset + (programDuration N ops : ℝ)) t q.2]
  congr 1
  funext e
  congr 1
  simp only [program_duration_append, programDuration, add_zero, NNReal.coe_add, add_assoc]

#print axioms segment_readout_measurable
#print axioms calendar_readout_measurable
#print axioms complete_readout_measurable
#print axioms segment_joint_toMeasure
#print axioms calendar_joint_toMeasure
#print axioms completed_joint_toMeasure
#print axioms tail_joint_toMeasure
#print axioms finite_observed_fibre_kernel
#print axioms calendar_joint_cons
#print axioms completed_joint_bind_calendar
#print axioms tail_joint_cut_bind
#print axioms calendar_joint_nil
#print axioms program_duration_append
#print axioms calendar_joint_append
#print axioms calendar_joint_single
#print axioms actual_complete_calendar_cut_refinement

end CloudG3.ActualCalendarCutContext
