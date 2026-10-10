import G2LiteralEpochLaw
import UnifiedLean.Source.SourceProgramTransport

/-!
Actual calendar records built from original interval clocks and original
boundary operations. Contributor: dot (OpenAI), 6 October 2026.
The segment laws and finite-calendar endpoint/probability induction are
derived here. All-time path transport remains a subsequent obligation.
-/
namespace GProgram.G2.ActualCalendarTrace
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.LiteralEpochLaw
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

abbrev SegmentRecord (N : RootedBinary V E X) (sample : Copy → X) :=
  (Bool × ClockTrace N sample (Fintype.card Copy)) × Code N sample

def attachEndpoint (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample)
    (z : Bool × ClockTrace N sample (Fintype.card Copy)) : SegmentRecord N sample :=
  (z,traceEndpoint N (Fintype.card Copy) s z.2)

lemma trace_endpoint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) : Measurable (traceEndpoint N n s) := by
  cases n with
  | zero => exact measurable_const
  | succ n => exact (measurable_pi_apply (Fin.last n)).snd.snd

lemma attach_endpoint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Measurable (attachEndpoint N s) :=
  measurable_id.prodMk ((trace_endpoint_measurable N _ s).comp measurable_snd)

def boundaryRecord (N : RootedBinary V E X) {sample : Copy → X}
    (d : Code N sample) : SegmentRecord N sample :=
  ((true,emptyTrace N (Fintype.card Copy) d),d)

lemma boundary_record_measurable (N : RootedBinary V E X) {sample : Copy → X} :
    Measurable (boundaryRecord N (sample := sample)) := measurable_of_countable _

noncomputable def actualSegmentLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) :
    Measure (SegmentRecord N sample) :=
  match op with
  | .interval h => (actualMarkedTraceLaw N r (Fintype.card Copy) s (h : ℝ)).map (attachEndpoint N s)
  | .boundary b => (boundaryKernel N b s).toMeasure.map (boundaryRecord N)

theorem actual_segment_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) :
    IsProbabilityMeasure (actualSegmentLaw N r op s) := by
  cases op with
  | interval h =>
      letI := actual_marked_trace_probability N r (Fintype.card Copy) s h
      exact Measure.isProbabilityMeasure_map (attach_endpoint_measurable N s).aemeasurable
  | boundary b =>
      exact Measure.isProbabilityMeasure_map (boundary_record_measurable N).aemeasurable

/-- Forgetting the success flag is justified by the proved full-mass success
event, without changing exceptional trace endpoints in the definition. -/
theorem actual_trace_endpoint_source_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (h : ℝ≥0) :
    (actualMarkedTraceLaw N r (Fintype.card Copy) s (h : ℝ)).map
      (fun z => traceEndpoint N (Fintype.card Copy) s z.2) =
      (sourceTimeKernel N r h s).toMeasure := by
  let f : Option (Code N sample) → Code N sample := fun z => z.getD s
  have hf : Measurable f := measurable_of_countable _
  have he : (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
      traceEndpoint N (Fintype.card Copy) s z.2) =ᵐ[actualMarkedTraceLaw N r (Fintype.card Copy) s (h : ℝ)]
      (f ∘ decodedEndpoint N (Fintype.card Copy) s) := by
    filter_upwards [actual_marked_trace_success_ae N r (Fintype.card Copy) s h
      (Finset.card_le_univ s.val.live)] with z hz
    simp [Function.comp_def,f,decodedEndpoint,hz]
  rw [Measure.map_congr he,← Measure.map_map hf (decoded_endpoint_measurable N _ s)]
  change (actualEndpointLaw N r (Fintype.card Copy) s (h : ℝ)).map f = _
  rw [actual_endpoint_eq_literal_clock_pushforward,original_copy_cap_literal_epoch_law]
  rw [Measure.map_map hf (measurable_of_countable (some : Code N sample → Option (Code N sample)))]
  change ((sourceTimeKernel N r h s).toMeasure).map id = _
  exact Measure.map_id

/-- Both segment kinds recover the actual original source step, rather than
assuming a desired calendar endpoint law as an input. -/
theorem actual_segment_endpoint_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) :
    (actualSegmentLaw N r op s).map Prod.snd = (sourceProgramStep N r op s).toMeasure := by
  cases op with
  | interval h =>
      rw [actualSegmentLaw,Measure.map_map measurable_snd (attach_endpoint_measurable N s)]
      exact actual_trace_endpoint_source_law N r s h
  | boundary b =>
      rw [actualSegmentLaw,Measure.map_map measurable_snd (boundary_record_measurable N)]
      change ((boundaryKernel N b s).toMeasure).map id = _
      exact Measure.map_id

theorem segment_end_fibre_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s d : Code N sample) :
    actualSegmentLaw N r op s {z | z.2 = d} = sourceProgramStep N r op s d := by
  have he := congrArg (fun μ : Measure (Code N sample) => μ {d})
    (actual_segment_endpoint_law N r op s)
  rw [Measure.map_apply measurable_snd (MeasurableSet.singleton d),
    PMF.toMeasure_apply_singleton _ _ (by trivial)] at he
  exact he

def recordCons (N : RootedBinary V E X) {sample : Copy → X} (n : Nat)
    (z : SegmentRecord N sample × (Fin n → SegmentRecord N sample)) :
    Fin (n+1) → SegmentRecord N sample := Fin.cons z.1 z.2

lemma record_cons_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) : Measurable (recordCons N (sample := sample) n) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

noncomputable def actualCalendarTraceLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : (ops : List (ProgramStep N)) → Code N sample →
      Measure (Fin ops.length → SegmentRecord N sample)
  | [],_ => Measure.dirac (fun i => Fin.elim0 i)
  | op::ops,s => ∑ d : Code N sample,
      (((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
        (actualCalendarTraceLaw N r ops d)).map (recordCons N ops.length)

noncomputable def calendarEnd (N : RootedBinary V E X) {sample : Copy → X} :
    (ops : List (ProgramStep N)) → Code N sample →
      (Fin ops.length → SegmentRecord N sample) → Code N sample
  | [],s,_ => s
  | _::ops,_,z => calendarEnd N ops (z 0).2 (Fin.tail z)

#print axioms trace_endpoint_measurable
#print axioms attach_endpoint_measurable
#print axioms boundary_record_measurable
#print axioms actual_segment_probability
#print axioms actual_trace_endpoint_source_law
#print axioms actual_segment_endpoint_law
#print axioms segment_end_fibre_mass
#print axioms record_cons_measurable

lemma calendar_end_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (calendarEnd N ops s) := by
  induction ops generalizing s with
  | nil => exact measurable_const
  | cons op ops ih =>
      have hm : Measurable (fun z : Code N sample × (Fin ops.length → SegmentRecord N sample) =>
          calendarEnd N ops z.1 z.2) := measurable_from_prod_countable_right ih
      have ht : Measurable (Fin.tail : (Fin (op::ops).length → SegmentRecord N sample) →
          (Fin ops.length → SegmentRecord N sample)) :=
        measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)
      exact hm.comp (((measurable_pi_apply 0).snd).prodMk ht)

theorem actual_calendar_trace_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    IsProbabilityMeasure (actualCalendarTraceLaw N r ops s) := by
  induction ops generalizing s with
  | nil => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | cons op ops ih =>
      letI := actual_segment_probability N r op s
      have he (d : Code N sample) :
          ((((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
            (actualCalendarTraceLaw N r ops d)).map (recordCons N ops.length)) univ =
          sourceProgramStep N r op s d := by
        letI := ih d
        have htail : (actualCalendarTraceLaw N r ops d) univ = 1 := measure_univ
        rw [Measure.map_apply (record_cons_measurable N _) MeasurableSet.univ,
          preimage_univ,← univ_prod_univ,Measure.prod_prod,htail,mul_one,
          Measure.restrict_apply MeasurableSet.univ,univ_inter,segment_end_fibre_mass]
      constructor
      calc
        (actualCalendarTraceLaw N r (op::ops) s) univ =
            ∑ d : Code N sample, sourceProgramStep N r op s d := by
          rw [actualCalendarTraceLaw,Measure.finsetSum_apply]
          exact Finset.sum_congr rfl (fun d _ => he d)
        _ = 1 := by
          simpa only [tsum_fintype] using (PMF.tsum_coe (sourceProgramStep N r op s))

/-- The restriction forces exactly the current terminal state before the
tail compiler is read. This uses the actual joint segment measure. -/
theorem calendar_branch_endpoint_map (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (ops : List (ProgramStep N))
    (s d : Code N sample) :
    (((((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
        (actualCalendarTraceLaw N r ops d)).map (recordCons N ops.length)).map
          (calendarEnd N (op::ops) s)) =
      sourceProgramStep N r op s d •
        ((actualCalendarTraceLaw N r ops d).map (calendarEnd N ops d)) := by
  letI := actual_segment_probability N r op s
  letI := actual_calendar_trace_probability N r ops d
  let F : SegmentRecord N sample × (Fin ops.length → SegmentRecord N sample) → Code N sample :=
    fun z => calendarEnd N ops z.1.2 z.2
  let G : SegmentRecord N sample × (Fin ops.length → SegmentRecord N sample) → Code N sample :=
    fun z => calendarEnd N ops d z.2
  have hF : Measurable F := by
    have hm : Measurable (fun z : Code N sample × (Fin ops.length → SegmentRecord N sample) =>
        calendarEnd N ops z.1 z.2) :=
      measurable_from_prod_countable_right (fun e => calendar_end_measurable N ops e)
    exact hm.comp (measurable_fst.snd.prodMk measurable_snd)
  have hG : Measurable G := (calendar_end_measurable N ops d).comp measurable_snd
  have hA : MeasurableSet {z : SegmentRecord N sample | z.2 = d} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have he : F =ᵐ[((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
      (actualCalendarTraceLaw N r ops d)] G := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hF hG)).mpr
    filter_upwards [ae_restrict_mem hA] with z hz
    exact Filter.Eventually.of_forall (fun tail => by dsimp [F,G]; rw [hz])
  rw [Measure.map_map (calendar_end_measurable N _ s) (record_cons_measurable N _)]
  change ((((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
    (actualCalendarTraceLaw N r ops d)).map F) = _
  rw [Measure.map_congr he]
  change ((((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
    (actualCalendarTraceLaw N r ops d)).map ((calendarEnd N ops d) ∘ Prod.snd)) = _
  rw [← Measure.map_map (calendar_end_measurable N ops d) measurable_snd,
    Measure.map_snd_prod,Measure.map_smul,Measure.restrict_apply MeasurableSet.univ,
    univ_inter,segment_end_fibre_mass]

theorem actual_calendar_endpoint_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (actualCalendarTraceLaw N r ops s).map (calendarEnd N ops s) =
      (sourceProgram N r ops s).toMeasure := by
  induction ops generalizing s with
  | nil =>
      rw [actualCalendarTraceLaw,Measure.map_dirac' (calendar_end_measurable N [] s)]
      simp [calendarEnd,sourceProgram,PMF.toMeasure_pure]
  | cons op ops ih =>
      rw [actualCalendarTraceLaw,
        Measure.map_finset_sum' (calendar_end_measurable N (op::ops) s).aemeasurable]
      simp_rw [calendar_branch_endpoint_map,ih]
      apply Measure.ext
      intro A hA
      rw [Measure.finsetSum_apply,sourceProgram,PMF.toMeasure_bind_apply _ _ A hA,tsum_fintype]
      simp only [Measure.smul_apply,smul_eq_mul]

theorem calendar_end_fibre_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s d : Code N sample) :
    actualCalendarTraceLaw N r ops s {z | calendarEnd N ops s z = d} =
      sourceProgram N r ops s d := by
  have he := congrArg (fun μ : Measure (Code N sample) => μ {d})
    (actual_calendar_endpoint_law N r ops s)
  rw [Measure.map_apply (calendar_end_measurable N ops s) (MeasurableSet.singleton d),
    PMF.toMeasure_apply_singleton _ _ (by trivial)] at he
  exact he

#print axioms calendar_end_measurable
#print axioms actual_calendar_trace_probability
#print axioms calendar_branch_endpoint_map
#print axioms actual_calendar_endpoint_law
#print axioms calendar_end_fibre_mass
end GProgram.G2.ActualCalendarTrace
