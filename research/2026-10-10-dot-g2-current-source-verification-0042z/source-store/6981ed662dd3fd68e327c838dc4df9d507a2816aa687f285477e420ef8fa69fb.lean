import G2RootedTimedOutputSupport

/-!
Fixed-boundary nullity for the entire actual calendar and ancestral trace.
Contributor: dot (OpenAI), 6 October 2026.
Offsets are the existing accumulated original calendar durations. A fixed
absolute age is avoided by all actual active graft records simultaneously.
-/
namespace GProgram.G2.AssembledBoundaryNull
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.NativeParentRouting
open GProgram.G2.ClockBoundaryNull GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.ActualCalendarTrace GProgram.G2.FiniteAncestralTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.ChronologicalPathReadout
open GProgram.G2.CalendarDecoration GProgram.G2.ControlledTraceAssembly
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.LiteralMarkedClockTrace.choiceOptionMeasurable

noncomputable def TraceAvoid (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (offset age : ℝ) (z : ClockTrace N sample n) : Prop :=
  ∀ i, (z i).1 = true → offset+(z i).2.1 ≠ age

lemma trace_avoid_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (offset age : ℝ) : Measurable (TraceAvoid N (sample := sample) n offset age) := by
  apply Measurable.forall
  intro i
  exact (((measurable_pi_apply i).fst).eq measurable_const).imp
    (((measurable_const.add (measurable_pi_apply i).snd.fst).eq measurable_const).not)

noncomputable def SegmentAvoid (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (offset age : ℝ) (z : SegmentRecord N sample) : Prop :=
  match op with
  | .boundary _ => True
  | .interval _ => TraceAvoid N (Fintype.card Copy) offset age z.1.2

lemma segment_avoid_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (offset age : ℝ) : MeasurableSet {z : SegmentRecord N sample | SegmentAvoid N op offset age z} := by
  cases op with
  | boundary b => exact MeasurableSet.univ
  | interval h => exact ((trace_avoid_measurable N _ offset age).comp measurable_fst.snd).setOf

lemma actual_segment_avoids (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) (offset age : ℝ) :
    ∀ᵐ z ∂actualSegmentLaw N r op s, SegmentAvoid N op offset age z := by
  cases op with
  | boundary b => exact Filter.Eventually.of_forall (fun _ => True.intro)
  | interval h =>
      rw [actualSegmentLaw,actualMarkedTraceLaw,
        Measure.map_map (attach_endpoint_measurable N s) (marked_trace_measurable N _ s h),
        ae_map_iff ((attach_endpoint_measurable N s).comp (marked_trace_measurable N _ s h)).aemeasurable
          (segment_avoid_measurable N (.interval h) offset age)]
      filter_upwards [actual_active_times_avoid_fixed N r s (age-offset)] with c hc
      intro i hi he
      have hn := hc (Fintype.card Copy) h i hi
      apply hn
      change offset + ((literalMarkedTrace N (Fintype.card Copy) h s c).2 i).2.1 = age at he
      linarith

noncomputable def CalendarAvoid (N : RootedBinary V E X) {sample : Copy → X} :
    (ops : List (ProgramStep N)) → ℝ → ℝ → (Fin ops.length → SegmentRecord N sample) → Prop
  | [],_,_,_ => True
  | op::ops,offset,age,z => SegmentAvoid N op offset age (z 0) ∧
      CalendarAvoid N ops (offset+stepDuration N op) age (Fin.tail z)

lemma calendar_avoid_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (offset age : ℝ) :
    MeasurableSet {z : Fin ops.length → SegmentRecord N sample | CalendarAvoid N ops offset age z} := by
  induction ops generalizing offset with
  | nil => exact MeasurableSet.univ
  | cons op ops ih =>
      have ht : Measurable (Fin.tail : (Fin (op::ops).length → SegmentRecord N sample) →
          (Fin ops.length → SegmentRecord N sample)) := measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)
      exact ((segment_avoid_measurable N (sample := sample) op offset age).preimage (measurable_pi_apply 0)).inter
        ((ih (offset+stepDuration N op)).preimage ht)

lemma actual_calendar_avoids (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (offset age : ℝ) :
    ∀ᵐ z ∂actualCalendarTraceLaw N r ops s, CalendarAvoid N ops offset age z := by
  induction ops generalizing s offset with
  | nil => exact Filter.Eventually.of_forall (fun _ => True.intro)
  | cons op ops ih =>
      rw [actualCalendarTraceLaw,ae_finsetSum_measure_iff]
      intro d _
      letI := actual_segment_probability N r op s
      letI := actual_calendar_trace_probability N r ops d
      have hm := (calendar_avoid_measurable N (sample := sample) (op::ops) offset age).preimage (record_cons_measurable N _)
      apply (ae_map_iff (record_cons_measurable N _).aemeasurable
        (calendar_avoid_measurable N (sample := sample) (op::ops) offset age)).mpr
      apply (Measure.ae_prod_iff_ae_ae hm).mpr
      filter_upwards [ae_restrict_of_ae (actual_segment_avoids N r op s offset age)] with z hz
      filter_upwards [ih d (offset+stepDuration N op)] with tail ht
      exact ⟨hz,ht⟩

lemma actual_tail_avoids (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (offset age : ℝ) :
    ∀ᵐ z ∂completeAncestralTraceLaw N r s, TraceAvoid N (Fintype.card Copy) offset age z.2 := by
  rw [completeAncestralTraceLaw]
  apply (ae_map_iff (complete_ancestral_trace_measurable N s).aemeasurable
    (((trace_avoid_measurable N _ offset age).comp measurable_snd).setOf)).mpr
  filter_upwards [actual_active_times_avoid_fixed N r s (age-offset)] with c hc
  intro i hi he
  have hn := hc (Fintype.card Copy) (clockCover N s c) i hi
  apply hn
  change offset + ((literalMarkedTrace N (Fintype.card Copy) (clockCover N s c) s c).2 i).2.1 = age at he
  linarith

noncomputable def CompleteAvoid (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (offset age : ℝ) (z : CompleteCalendarRecord N sample ops) : Prop :=
  CalendarAvoid N ops offset age z.2.1 ∧ TraceAvoid N (Fintype.card Copy) (offset+programDuration N ops) age z.2.2.2

lemma complete_avoid_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (offset age : ℝ) : MeasurableSet {z : CompleteCalendarRecord N sample ops | CompleteAvoid N ops offset age z} :=
  ((calendar_avoid_measurable N ops offset age).preimage measurable_snd.fst).inter
    (((trace_avoid_measurable N _ (offset+programDuration N ops) age).comp measurable_snd.snd.snd).setOf)

/-- A fixed absolute age is avoided by every active event of the complete
actual source trace on one full-measure event, including its random tail. -/
theorem actual_complete_avoids_fixed_age (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (offset age : ℝ) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s, CompleteAvoid N ops offset age z := by
  rw [completeCalendarTraceLaw,ae_finsetSum_measure_iff]
  intro d _
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have hm := complete_avoid_measurable N (sample := sample) ops offset age
  have hmap : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) := measurable_const.prodMk measurable_id
  apply (ae_map_iff hmap.aemeasurable hm).mpr
  apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
  filter_upwards [ae_restrict_of_ae (actual_calendar_avoids N r ops s offset age)] with past hp
  filter_upwards [actual_tail_avoids N r d (offset+programDuration N ops) age] with tail ht
  exact ⟨hp,ht⟩

/-- All original demographic node dates are handled simultaneously through
actual terminal fibres and the original once-drawn joint register law. -/
theorem actual_registered_original_boundary_null (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (ρ : PMF (V → Bool)) :
    ∀ᵐ z ∂registeredTraceLaw N sample r (compiledCalendarProgram N C H gamma common) ρ,
      ∀ v : V, CompleteAvoid N (compiledCalendarProgram N C H gamma common)
        (firstOriginalDate N C) (C.age v) z.2 := by
  apply ae_all_iff.mpr
  intro v
  let ops := compiledCalendarProgram N C H gamma common
  have hm := (complete_avoid_measurable N (sample := sample) ops (firstOriginalDate N C) (C.age v)).preimage
    (measurable_snd : Measurable (Prod.snd : RegisteredRecord N sample ops → CompleteCalendarRecord N sample ops))
  rw [registeredTraceLaw,ae_finsetSum_measure_iff]
  intro reg _
  apply Measure.ae_smul_measure
  apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hm).mpr
  exact actual_complete_avoids_fixed_age N r ops (initialCode N sample reg) (firstOriginalDate N C) (C.age v)

#print axioms actual_registered_original_boundary_null
end GProgram.G2.AssembledBoundaryNull
