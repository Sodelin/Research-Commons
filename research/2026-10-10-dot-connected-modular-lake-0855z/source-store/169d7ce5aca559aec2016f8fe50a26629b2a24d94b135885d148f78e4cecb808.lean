import G2TimedBoundMeasurability
import G2JointTimedObservation

/-!
Strict chronological support of the actual completed original calendar.
Contributor: dot (OpenAI), 7 October 2026.
The calendar invariant uses the original safe-step support and exact endpoint
fibres. The ancestral tail uses actual strictly positive clocks. A finite
natural bound is derived after the run; no desired timed output is assumed.
-/
namespace GProgram.G2.ChronologicalPathReadout
open scoped NNReal
open Nanuq.Source UnifiedLean.Source.SourceProgramTransport
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
/-- Duration interface used by the unchanged assembled boundary-null consumer.
It is exactly the duration of the corresponding singleton program. -/
noncomputable def stepDuration (N : RootedBinary V E X) (op : ProgramStep N) : ℝ≥0 :=
  programDuration N [op]
end GProgram.G2.ChronologicalPathReadout

namespace GProgram.G2.CompleteTimedSupport
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.FiniteSourceSnapshot
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.ActualDecorationFold GProgram.G2.CalendarDecoration
open GProgram.G2.DecorationMeasurability
open GProgram.G2.ChronologicalDecoration GProgram.G2.StrictClockDecoration
open GProgram.G2.OriginalProgramSafety GProgram.G2.TimedBoundMeasurability
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.FiniteAncestralTrace
open GProgram.G2.CompleteDecoration GProgram.G2.ChronologicalPathReadout
open GProgram.G2.ClockBoundaryNull
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Countable cofinal bounds expose a measurable chronological-support event. -/
def HasTimedBound (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) : Prop := ∃ n : ℕ, TimedBound leafAge M s (n : ℝ)

lemma has_timed_bound_of_bound (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) (b : ℝ) (hb : TimedBound leafAge M s b) :
    HasTimedBound leafAge M s := by
  obtain ⟨n,hn⟩ := exists_nat_gt b
  exact ⟨n,timed_bound_mono leafAge M s hn.le hb⟩

lemma has_timed_bound_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) :
    Measurable (fun z : Code N sample × (Copy → Copy → ℝ) =>
      HasTimedBound leafAge z.2 (state z.1)) := by
  apply Measurable.exists
  intro n
  exact (timed_bound_joint_measurable N leafAge).comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

theorem actual_boundary_timed_bound (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ) (b : BoundaryOperation N)
    (s : Code N sample) (bound : ℝ) (hM : TimedBound leafAge M (state s) bound) :
    ∀ᵐ d ∂(boundaryKernel N b s).toMeasure, TimedBound leafAge M (state d) bound := by
  have hm : MeasurableSet {d : Code N sample | TimedBound leafAge M (state d) bound} :=
    ((timed_bound_joint_measurable N leafAge).comp
      (measurable_id.prodMk (measurable_const.prodMk measurable_const))).setOf
  have hp (H : GProgram.G2.OriginalHybridParents N)
      (coin : AtNode (state s) H.hybrid → Bool) :
      TimedBound leafAge M (state (pulseCode H s coin)) bound :=
    snapshot_preserves_timed_bound N.root (pulse H (state s) coin)
      (pulse_source_valid H sample (state s) s.property coin).forest leafAge M bound hM
  cases b with
  | exit e =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      exact snapshot_preserves_timed_bound N.root (exitEdge N (state s) e)
        (exitEdge_source_valid N sample (state s) s.property e).forest leafAge M bound hM
  | ordinary e degree =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      exact snapshot_preserves_timed_bound N.root (enterEdge N (state s) e)
        (enterEdge_source_valid N sample (state s) s.property e).forest leafAge M bound hM
  | root =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      exact snapshot_preserves_timed_bound N.root (enterRoot N (state s))
        (enterRoot_source_valid N sample (state s) s.property).forest leafAge M bound hM
  | common H =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      exact hp H (fun _ => (state s).register H.hybrid)
  | independent H gamma =>
      rw [boundaryKernel,independentPulseKernel,
        ← PMF.toMeasure_map _ _ (measurable_of_countable (pulseCode H s))]
      apply (ae_map_iff (measurable_of_countable (pulseCode H s)).aemeasurable hm).mpr
      exact Filter.Eventually.of_forall (hp H)

noncomputable def SegmentCompatible (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (op : ProgramStep N) (offset : ℝ) (s : Code N sample) : Prop :=
  match op with
  | .interval h => EpochCompatible N C offset (offset+(h : ℝ)) (state s)
  | .boundary _ => True

theorem actual_segment_timed_bound (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (op : ProgramStep N)
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (he : SegmentCompatible N C op offset s)
    (hM : TimedBound (fun x => C.age (N.leaf (sample x))) M (state s) offset) :
    ∀ᵐ z ∂actualSegmentLaw N r op s,
      TimedBound (fun x => C.age (N.leaf (sample x)))
        (segmentMatrix N op s offset M z) (state z.2) (segmentOffset N op offset) := by
  have hm : MeasurableSet {z : SegmentRecord N sample |
      TimedBound (fun x => C.age (N.leaf (sample x)))
        (segmentMatrix N op s offset M z) (state z.2) (segmentOffset N op offset)} :=
    ((timed_bound_joint_measurable N _).comp
      (measurable_snd.prodMk (measurable_const.prodMk
        (segment_matrix_measurable N op s offset M)))).setOf
  cases op with
  | interval h =>
      have ht := marked_trace_measurable N (Fintype.card Copy) s (h : ℝ)
      rw [actualSegmentLaw,actualMarkedTraceLaw,
        Measure.map_map (attach_endpoint_measurable N s) ht]
      apply (ae_map_iff ((attach_endpoint_measurable N s).comp ht).aemeasurable hm).mpr
      exact actual_clock_fold_chronological_ae N C r (Fintype.card Copy) s
        offset (offset+(h : ℝ)) (h : ℝ) offset he le_rfl h.property M hM
  | boundary b =>
      rw [actualSegmentLaw]
      apply (ae_map_iff (boundary_record_measurable N).aemeasurable hm).mpr
      exact actual_boundary_timed_bound N _ M b s offset hM

lemma calendar_timed_bound_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) :
    MeasurableSet {past | TimedBound leafAge (calendarMatrix N ops s offset M past)
      (state (calendarEnd N ops s past)) (offset+(programDuration N ops : ℝ))} :=
  ((timed_bound_joint_measurable N leafAge).comp
    ((calendar_end_measurable N ops s).prodMk
      (measurable_const.prodMk (calendar_matrix_measurable N ops s offset M)))).setOf

/-- Safety of each interval is required only on positive original endpoint
fibres. Null fibres vanish without normalization or conditional resampling. -/
theorem actual_calendar_timed_bound (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hs : SafeSteps N C r offset ops s)
    (hM : TimedBound (fun x => C.age (N.leaf (sample x))) M (state s) offset) :
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s,
      TimedBound (fun x => C.age (N.leaf (sample x)))
        (calendarMatrix N ops s offset M past) (state (calendarEnd N ops s past))
        (offset+(programDuration N ops : ℝ)) := by
  induction ops generalizing s offset M with
  | nil =>
      filter_upwards [] with past
      simpa only [calendarMatrix,calendarEnd,programDuration,NNReal.coe_zero,add_zero] using hM
  | cons op ops ih =>
      have hseg : SegmentCompatible N C op offset s := by
        cases op with
        | interval _ => exact hs.1
        | boundary _ => trivial
      have hnext : ∀ d, sourceProgramStep N r op s d ≠ 0 →
          SafeSteps N C r (segmentOffset N op offset) ops d := by
        intro d hd
        have hd' := (PMF.mem_support_iff _ _).mpr hd
        cases op with
        | interval _ => exact hs.2 d hd'
        | boundary _ => exact hs d hd'
      have hoff : segmentOffset N op offset+(programDuration N ops : ℝ) =
          offset+(programDuration N (op::ops) : ℝ) := by
        cases op <;> simp [segmentOffset,programDuration,add_assoc]
      rw [actualCalendarTraceLaw,ae_finsetSum_measure_iff]
      intro d _
      by_cases hd : sourceProgramStep N r op s d = 0
      · have hz : (actualSegmentLaw N r op s).restrict {z | z.2 = d} = 0 :=
          Measure.restrict_eq_zero.mpr (by rw [segment_end_fibre_mass,hd])
        simp [hz]
      · letI := actual_segment_probability N r op s
        letI := actual_calendar_trace_probability N r ops d
        have hm := calendar_timed_bound_measurable N
          (fun x => C.age (N.leaf (sample x))) (op::ops) s offset M
        have hmap := record_cons_measurable N (sample := sample) ops.length
        apply (ae_map_iff hmap.aemeasurable hm).mpr
        apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
        filter_upwards [ae_restrict_of_ae (actual_segment_timed_bound N C r op s offset M hseg hM),
          ae_restrict_mem (measurableSet_eq_fun measurable_snd measurable_const)] with z hz he
        have hD : TimedBound (fun x => C.age (N.leaf (sample x)))
            (segmentMatrix N op s offset M z) (state d) (segmentOffset N op offset) := by
          simpa only [show z.2 = d from he] using hz
        change ∀ᵐ tail ∂actualCalendarTraceLaw N r ops d,
          TimedBound (fun x => C.age (N.leaf (sample x)))
            (calendarMatrix N ops z.2 (segmentOffset N op offset)
              (segmentMatrix N op s offset M z) tail)
            (state (calendarEnd N ops z.2 tail))
            (offset+(programDuration N (op::ops) : ℝ))
        rw [show z.2 = d from he,←hoff]
        exact ih d (segmentOffset N op offset) (segmentMatrix N op s offset M z) (hnext d hd) hD

lemma duration_append (N : RootedBinary V E X) (a b : List (ProgramStep N)) :
    programDuration N (a++b) = programDuration N a+programDuration N b := by
  induction a with
  | nil => simp [programDuration]
  | cons op ops ih => cases op <;> simp [programDuration,ih,add_assoc]

lemma duration_boundaries (N : RootedBinary V E X) (bs : List (ProgramStep N))
    (hb : ∀ op ∈ bs, ∃ b, op = ProgramStep.boundary b) : programDuration N bs = 0 := by
  induction bs with
  | nil => rfl
  | cons op bs ih =>
      obtain ⟨b,rfl⟩ := hb op List.mem_cons_self
      exact ih (fun op hop => hb op (List.mem_cons_of_mem _ hop))

lemma calendar_tail_reaches (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (dates : List ℝ) (a : ℝ) :
    ∀ b ∈ dates, b ≤ a+(programDuration N (calendarTail N C H gamma common a dates) : ℝ) := by
  induction dates generalizing a with
  | nil => simp
  | cons b bs ih =>
      have hb : b ≤ a+(Real.toNNReal (b-a) : ℝ) := by
        have h := Real.le_coe_toNNReal (b-a)
        linarith
      have hd := duration_boundaries N (boundaryOperations N C H gamma common b)
        (original_batch_only_boundaries N C H gamma common b)
      intro c hc
      simp only [calendarTail,programDuration,duration_append,hd,zero_add,NNReal.coe_add]
      rcases List.mem_cons.mp hc with hc | hc
      · subst c
        have hn := (programDuration N (calendarTail N C H gamma common b bs)).property
        linarith
      · have hi := ih b c hc
        linarith

/-- The compiled original agenda has already reached the root date before
ancestral completion. Only this inequality, rather than an artificial tail
cutoff or a desired age identity, is needed for strict tail decoration. -/
lemma original_program_reaches_root (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) :
    C.age N.root ≤ firstOriginalDate N C+
      (programDuration N (compiledCalendarProgram N C H gamma common) : ℝ) := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro he
    have hm := original_date_scheduled N C N.root
    rw [he] at hm
    exact List.not_mem_nil hm
  obtain ⟨a,dates,he⟩ := List.exists_cons_of_ne_nil hne
  have hf : a = firstOriginalDate N C := by
    simpa only [he,List.getElem_cons_zero] using first_compiled_date_is_initial_boundary N C
  have hd := duration_boundaries N (boundaryOperations N C H gamma common a)
    (original_batch_only_boundaries N C H gamma common a)
  rw [compiledCalendarProgram,he,duration_append,hd,zero_add,←hf]
  have hm := original_date_scheduled N C N.root
  rw [he] at hm
  rcases List.mem_cons.mp hm with hm | hm
  · rw [hm]
    exact le_add_of_nonneg_right (programDuration N _).property
  · exact calendar_tail_reaches N C H gamma common dates a _ hm
/-- The finite literal ancestral tail has a chronological decoration at some
finite bound, under the original clock law and an actual ancestral root. -/
theorem actual_tail_timed_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (offset : ℝ)
    (hs : AncestralRoot N s) (ha : C.age N.root ≤ offset) (M : Copy → Copy → ℝ)
    (hM : TimedBound (fun x => C.age (N.leaf (sample x))) M (state s) offset) :
    ∀ᵐ z ∂completeAncestralTraceLaw N r s,
      HasTimedBound (fun x => C.age (N.leaf (sample x)))
        (foldMatrix N (Fintype.card Copy) s offset M z.2)
        (state (traceEndpoint N (Fintype.card Copy) s z.2)) := by
  have hf : Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
      foldMatrix N (Fintype.card Copy) s offset M z.2) :=
    (fold_matrix_joint_measurable N _).comp (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_snd)))
  have he : Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
      traceEndpoint N (Fintype.card Copy) s z.2) :=
    (trace_end_joint_measurable N _).comp (measurable_const.prodMk measurable_snd)
  have hm := ((has_timed_bound_joint_measurable N
    (fun x => C.age (N.leaf (sample x)))).comp (he.prodMk hf)).setOf
  rw [completeAncestralTraceLaw]
  apply (ae_map_iff (complete_ancestral_trace_measurable N s).aemeasurable hm).mpr
  filter_upwards [actual_current_clock_regular_ae N r s,actual_clock_strictly_positive N r s]
    with c hc hp
  have hepoch : EpochCompatible N C offset offset (state s) := by
    intro x
    rw [hs x]
    exact ⟨rfl,ha⟩
  exact has_timed_bound_of_bound _ _ _ (offset+(clockCover N s c : ℝ))
    (literal_fold_timed_bound N C (Fintype.card Copy) s offset offset
      (clockCover N s c : ℝ) offset c hc hp hepoch le_rfl (clockCover N s c).property M hM)

lemma complete_timed_support_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) :
    MeasurableSet {z | HasTimedBound leafAge (completeMatrix N ops s offset M z)
      (state (completeEnd N ops z))} :=
  ((has_timed_bound_joint_measurable N leafAge).comp
    ((complete_end_measurable N ops).prodMk (complete_matrix_measurable N ops s offset M))).setOf

theorem actual_complete_timed_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hs : SafeSteps N C r offset ops s)
    (hM : TimedBound (fun x => C.age (N.leaf (sample x))) M (state s) offset)
    (ha : C.age N.root ≤ offset+(programDuration N ops : ℝ))
    (hroot : ∀ d, sourceProgram N r ops s d ≠ 0 → AncestralRoot N d) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s,
      HasTimedBound (fun x => C.age (N.leaf (sample x)))
        (completeMatrix N ops s offset M z) (state (completeEnd N ops z)) := by
  rw [completeCalendarTraceLaw,ae_finsetSum_measure_iff]
  intro d _
  by_cases hd : sourceProgram N r ops s d = 0
  · have hz : (actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d} = 0 :=
      Measure.restrict_eq_zero.mpr (by rw [calendar_end_fibre_mass,hd])
    simp [hz]
  · letI := actual_calendar_trace_probability N r ops s
    letI := complete_ancestral_trace_probability N r d
    have hmap : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
        (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) :=
      measurable_const.prodMk measurable_id
    have hm := complete_timed_support_measurable N (fun x => C.age (N.leaf (sample x))) ops s offset M
    apply (ae_map_iff hmap.aemeasurable hm).mpr
    apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
    filter_upwards [ae_restrict_of_ae (actual_calendar_timed_bound N C r ops s offset M hs hM),
      ae_restrict_mem (measurableSet_eq_fun (calendar_end_measurable N ops s) measurable_const)] with past hp he
    have hD : TimedBound (fun x => C.age (N.leaf (sample x)))
        (calendarMatrix N ops s offset M past) (state d) (offset+(programDuration N ops : ℝ)) := by
      simpa only [show calendarEnd N ops s past = d from he] using hp
    exact actual_tail_timed_support N C r d (offset+(programDuration N ops : ℝ))
      (hroot d hd) ha (calendarMatrix N ops s offset M past) hD

/-- Unchanged physical consumer interface. Every premise of the generic
calendar/tail result is discharged by the original initialized compiler. -/
theorem actual_original_complete_timed_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register),
      HasTimedBound (fun x => C.age (N.leaf (sample x)))
        (completeMatrix N (compiledCalendarProgram N C H gamma common)
          (initialCode N sample register) (firstOriginalDate N C)
          (fun x _ => C.age (N.leaf (sample x))) z)
        (state (completeEnd N (compiledCalendarProgram N C H gamma common) z)) := by
  apply actual_complete_timed_support N C r _ _ _ _
    (actual_original_program_safe N C sample register H gamma common r)
  · exact snapshot_preserves_timed_bound N.root (initial N sample register)
      (initial_source_valid N sample register).forest _ _ _
      (initial_timed_bound N sample register _ _)
  · exact original_program_reaches_root N C H gamma common
  · intro d hd
    exact initialized_original_calendar_ancestral_support N C sample register H gamma common r
      ((PMF.mem_support_iff _ _).mpr hd)

#print axioms has_timed_bound_of_bound
#print axioms has_timed_bound_joint_measurable
#print axioms actual_boundary_timed_bound
#print axioms actual_segment_timed_bound
#print axioms actual_calendar_timed_bound
#print axioms duration_append
#print axioms calendar_tail_reaches
#print axioms original_program_reaches_root
#print axioms actual_tail_timed_support
#print axioms actual_complete_timed_support
#print axioms actual_original_complete_timed_support
end GProgram.G2.CompleteTimedSupport
