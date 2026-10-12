import G2DecorationMeasurability
import G2ChronologicalPathReadout

/-!
Literal same-record decoration through the original finite calendar.
Contributor: dot (OpenAI), 7 October 2026.

Interval folds read the recorded active mergers and their original offsets.
Boundary steps retain the matrix and advance to the actual stored endpoint.
Boundary preservation is derived from the original population transports and
snapshot coding. The actual-calendar invariant uses unnormalized terminal
fibres and finite product measures, without success or chronology premises.
-/
namespace GProgram.G2.CalendarDecoration
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.FiniteSourceSnapshot
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.SourceGraftDecoration GProgram.G2.ActualDecorationFold
open GProgram.G2.DecorationMeasurability
open scoped Classical NNReal BigOperators

/-- The standard finite a.e. sum identity, exposed in the membership form used
by the preserved consumer. Measures and predicates need no finiteness,
measurability or nonzero-mass premise beyond the finite index set itself. -/
lemma ae_finsetSum_measure_iff {α ι : Type*} [MeasurableSpace α]
    {p : α → Prop} {I : Finset ι} {μ : ι → Measure α} :
    (∀ᵐ x ∂∑ i ∈ I, μ i, p x) ↔ ∀ i ∈ I, ∀ᵐ x ∂μ i, p x :=
  MeasureTheory.ae_finsetSum_measure_iff

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

noncomputable def segmentOffset (N : RootedBinary V E X) (op : ProgramStep N) (offset : ℝ) : ℝ :=
  match op with
  | .interval h => offset+(h : ℝ)
  | .boundary _ => offset

noncomputable def segmentMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (z : SegmentRecord N sample) : Copy → Copy → ℝ :=
  match op with
  | .interval _ => foldMatrix N (Fintype.card Copy) s offset M z.1.2
  | .boundary _ => M

noncomputable def calendarMatrix (N : RootedBinary V E X) {sample : Copy → X} :
    (ops : List (ProgramStep N)) → Code N sample → ℝ → (Copy → Copy → ℝ) →
      (Fin ops.length → SegmentRecord N sample) → (Copy → Copy → ℝ)
  | [],_,_,M,_ => M
  | op::ops,s,offset,M,past => calendarMatrix N ops (past 0).2
      (segmentOffset N op offset) (segmentMatrix N op s offset M (past 0)) (Fin.tail past)

lemma calendar_matrix_interval (N : RootedBinary V E X) {sample : Copy → X}
    (h : ℝ≥0) (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) (past : Fin (.interval h::ops).length → SegmentRecord N sample) :
    calendarMatrix N (.interval h::ops) s offset M past =
      calendarMatrix N ops (past 0).2 (offset+(h : ℝ))
        (foldMatrix N (Fintype.card Copy) s offset M (past 0).1.2) (Fin.tail past) := rfl

lemma calendar_matrix_boundary (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) (past : Fin (.boundary b::ops).length → SegmentRecord N sample) :
    calendarMatrix N (.boundary b::ops) s offset M past =
      calendarMatrix N ops (past 0).2 offset M (Fin.tail past) := rfl

lemma segment_matrix_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) :
    Measurable (fun z : Code N sample ×
      (ℝ × ((Copy → Copy → ℝ) × SegmentRecord N sample)) =>
        segmentMatrix N op z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  cases op with
  | interval h =>
      exact (fold_matrix_joint_measurable N (Fintype.card Copy)).comp
        (measurable_fst.prodMk (measurable_snd.fst.prodMk
          (measurable_snd.snd.fst.prodMk measurable_snd.snd.snd.fst.snd)))
  | boundary b => exact measurable_snd.snd.fst

lemma segment_matrix_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    Measurable (segmentMatrix N op s offset M) :=
  (segment_matrix_joint_measurable N op).comp
    (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_id)))

/-- Joint measurability includes the carried real offset and real matrix;
only the original finite source code uses its discrete sigma-algebra. -/
lemma calendar_matrix_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) :
    Measurable (fun z : Code N sample ×
      (ℝ × ((Copy → Copy → ℝ) × (Fin ops.length → SegmentRecord N sample))) =>
        calendarMatrix N ops z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  induction ops with
  | nil => exact measurable_snd.snd.fst
  | cons op ops ih =>
      have hh : Measurable (fun z : Code N sample ×
          (ℝ × ((Copy → Copy → ℝ) × (Fin (op::ops).length → SegmentRecord N sample))) =>
          z.2.2.2 0) := (measurable_pi_apply 0).comp measurable_snd.snd.snd
      have ht : Measurable (fun z : Code N sample ×
          (ℝ × ((Copy → Copy → ℝ) × (Fin (op::ops).length → SegmentRecord N sample))) =>
          Fin.tail z.2.2.2) :=
        measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_snd.snd.snd)
      have hm : Measurable (fun z : Code N sample ×
          (ℝ × ((Copy → Copy → ℝ) × (Fin (op::ops).length → SegmentRecord N sample))) =>
          segmentMatrix N op z.1 z.2.1 z.2.2.1 (z.2.2.2 0)) :=
        (segment_matrix_joint_measurable N op).comp
          (measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk hh)))
      have ho : Measurable (fun z : Code N sample ×
          (ℝ × ((Copy → Copy → ℝ) × (Fin (op::ops).length → SegmentRecord N sample))) =>
          segmentOffset N op z.2.1) := by
        cases op with
        | interval h => exact measurable_snd.fst.add_const (h : ℝ)
        | boundary b => exact measurable_snd.fst
      exact ih.comp (hh.snd.prodMk (ho.prodMk (hm.prodMk ht)))

lemma calendar_matrix_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    Measurable (calendarMatrix N ops s offset M) :=
  (calendar_matrix_joint_measurable N ops).comp
    (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_id)))

/-- All original boundary operations preserve live genealogies. Snapshot
coding retains those genealogies, including the original shared-register and
current-owner independent pulse operations. -/
theorem actual_boundary_matrix_decorates (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ) (b : BoundaryOperation N)
    (s : Code N sample) (hM : ForestDecorates leafAge M (state s)) :
    ∀ᵐ d ∂(boundaryKernel N b s).toMeasure, ForestDecorates leafAge M (state d) := by
  have hm : MeasurableSet {d : Code N sample | ForestDecorates leafAge M (state d)} :=
    ((forest_decorates_joint_measurable N leafAge).comp
      (measurable_id.prodMk measurable_const)).setOf
  have hp (H : GProgram.G2.OriginalHybridParents N)
      (coin : AtNode (state s) H.hybrid → Bool) :
      ForestDecorates leafAge M (state (pulseCode H s coin)) :=
    snapshot_preserves_decorates N.root (pulse H (state s) coin)
      (pulse_source_valid H sample (state s) s.property coin).forest leafAge M hM
  cases b with
  | exit e =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      exact snapshot_preserves_decorates N.root (exitEdge N (state s) e)
        (exitEdge_source_valid N sample (state s) s.property e).forest leafAge M hM
  | ordinary e degree =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      exact snapshot_preserves_decorates N.root (enterEdge N (state s) e)
        (enterEdge_source_valid N sample (state s) s.property e).forest leafAge M hM
  | root =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      exact snapshot_preserves_decorates N.root (enterRoot N (state s))
        (enterRoot_source_valid N sample (state s) s.property).forest leafAge M hM
  | common H =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      exact hp H (fun _ => (state s).register H.hybrid)
  | independent H gamma =>
      rw [boundaryKernel,independentPulseKernel,
        ← PMF.toMeasure_map _ _ (measurable_of_countable (pulseCode H s))]
      apply (ae_map_iff (measurable_of_countable (pulseCode H s)).aemeasurable hm).mpr
      exact Filter.Eventually.of_forall (hp H)

/-- One actual segment folds its own trace and decorates its own stored
terminal state. The interval proof holds on every original clock vector. -/
theorem actual_segment_matrix_decorates (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (leafAge : Copy → ℝ) (op : ProgramStep N)
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hM : ForestDecorates leafAge M (state s)) :
    ∀ᵐ z ∂actualSegmentLaw N r op s,
      ForestDecorates leafAge (segmentMatrix N op s offset M z) (state z.2) := by
  have hm : MeasurableSet {z : SegmentRecord N sample |
      ForestDecorates leafAge (segmentMatrix N op s offset M z) (state z.2)} :=
    ((forest_decorates_joint_measurable N leafAge).comp
      (measurable_snd.prodMk (segment_matrix_measurable N op s offset M))).setOf
  cases op with
  | interval h =>
      have ht := marked_trace_measurable N (Fintype.card Copy) s (h : ℝ)
      rw [actualSegmentLaw,actualMarkedTraceLaw,
        Measure.map_map (attach_endpoint_measurable N s) ht]
      apply (ae_map_iff ((attach_endpoint_measurable N s).comp ht).aemeasurable hm).mpr
      exact Filter.Eventually.of_forall (fun c =>
        actual_literal_fold_decorates N (Fintype.card Copy) s (h : ℝ) offset c leafAge M hM)
  | boundary b =>
      rw [actualSegmentLaw]
      apply (ae_map_iff (boundary_record_measurable N).aemeasurable hm).mpr
      exact actual_boundary_matrix_decorates N leafAge M b s hM

lemma calendar_decoration_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) :
    MeasurableSet {past | ForestDecorates leafAge (calendarMatrix N ops s offset M past)
      (state (calendarEnd N ops s past))} :=
  ((forest_decorates_joint_measurable N leafAge).comp
    ((calendar_end_measurable N ops s).prodMk (calendar_matrix_measurable N ops s offset M))).setOf

/-- The finite calendar preserves decoration of the SAME actual terminal
forest, using unnormalized terminal fibres and the original record order.
No success, regularity, chronology, decoder or source-law premise is added. -/
theorem actual_calendar_matrix_decorates (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (leafAge : Copy → ℝ) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hM : ForestDecorates leafAge M (state s)) :
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s,
      ForestDecorates leafAge (calendarMatrix N ops s offset M past)
        (state (calendarEnd N ops s past)) := by
  induction ops generalizing s offset M with
  | nil => exact Filter.Eventually.of_forall (fun _ => hM)
  | cons op ops ih =>
      rw [actualCalendarTraceLaw,ae_finsetSum_measure_iff]
      intro d hd
      letI := actual_segment_probability N r op s
      letI := actual_calendar_trace_probability N r ops d
      have hm := calendar_decoration_measurable N leafAge (op::ops) s offset M
      have hmap := record_cons_measurable N (sample := sample) ops.length
      apply (ae_map_iff hmap.aemeasurable hm).mpr
      apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
      filter_upwards [ae_restrict_of_ae
        (actual_segment_matrix_decorates N r leafAge op s offset M hM),
        ae_restrict_mem (measurableSet_eq_fun measurable_snd measurable_const)] with z hz he
      have hD : ForestDecorates leafAge (segmentMatrix N op s offset M z) (state d) := by
        simpa only [show z.2 = d from he] using hz
      change ∀ᵐ tail ∂actualCalendarTraceLaw N r ops d,
        ForestDecorates leafAge (calendarMatrix N ops z.2 (segmentOffset N op offset)
          (segmentMatrix N op s offset M z) tail) (state (calendarEnd N ops z.2 tail))
      rw [show z.2 = d from he]
      exact ih d (segmentOffset N op offset) (segmentMatrix N op s offset M z) hD

#print axioms ae_finsetSum_measure_iff
#print axioms calendar_matrix_interval
#print axioms calendar_matrix_boundary
#print axioms segment_matrix_joint_measurable
#print axioms segment_matrix_measurable
#print axioms calendar_matrix_joint_measurable
#print axioms calendar_matrix_measurable
#print axioms actual_boundary_matrix_decorates
#print axioms actual_segment_matrix_decorates
#print axioms calendar_decoration_measurable
#print axioms actual_calendar_matrix_decorates
end GProgram.G2.CalendarDecoration
