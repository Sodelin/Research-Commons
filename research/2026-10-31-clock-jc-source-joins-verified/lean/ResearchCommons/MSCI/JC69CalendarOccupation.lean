import ResearchCommons.MSCI.JC69TraceOccupation
import ResearchCommons.MSCI.JC69BoundaryOccupation

/-! Later working extension; NOT in frozen occupation v1. UNCOMPILED.
The original calendar's state, records, matrices, kernel restrictions and
order are retained. This occupation identity neither certifies chronological
completion nor admits hidden-register routing into the scientific contract.
Contributor: dot (OpenAI), 30 October 2026. -/
noncomputable section
namespace ResearchCommons.MSCI.JC69CalendarOccupation
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.FiniteSourceSnapshot
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.ActualCalendarTrace GProgram.G2.ActualDecorationFold
open GProgram.G2.CalendarDecoration GProgram.G2.DecorationMeasurability
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open ResearchCommons.MSCI.JC69TraceOccupation ResearchCommons.MSCI.JC69BoundaryOccupation
open scoped Classical BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

lemma potential_decode_measurable (q : Copy → Base) (leafAge : Copy → ℝ)
    (tree : Genealogy Copy) :
    Measurable (fun z : (Copy → Copy → ℝ) × ℝ =>
      potential q leafAge tree (decode z.1 tree) z.2) := by
  induction tree with
  | leaf x => exact measurable_const.mul (measurable_snd.sub_const _)
  | graft a b ha hb =>
      have hr : Measurable (fun z : (Copy → Copy → ℝ) × ℝ =>
          z.1 (witness a) (witness b)) := by fun_prop
      have hA := ha.comp (measurable_fst.prodMk hr)
      have hB := hb.comp (measurable_fst.prodMk hr)
      exact (hA.add hB).add (measurable_const.mul (measurable_snd.sub hr))

lemma forest_potential_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (leafAge : Copy → ℝ) :
    Measurable (fun z : ((Copy → Copy → ℝ) × ℝ) × Code N sample =>
      forestPotential q leafAge (state z.2) z.1.1 z.1.2) := by
  apply measurable_from_prod_countable_left
  intro s
  change Measurable (fun x : (Copy → Copy → ℝ) × ℝ =>
    ∑ l ∈ (state s).live, potential q leafAge ((state s).genealogy l)
      (decode x.1 ((state s).genealogy l)) x.2)
  apply Finset.measurable_sum
  intro l _
  exact potential_decode_measurable q leafAge ((state s).genealogy l)

def segmentOccupation (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (op : ProgramStep N) (s : Code N sample)
    (z : SegmentRecord N sample) : ℝ :=
  match op with
  | .interval h => occupationAt N q (Fintype.card Copy) s 0 h z.1.2
  | .boundary _ => 0

lemma segment_occupation_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (op : ProgramStep N) (s : Code N sample) :
    Measurable (segmentOccupation N q op s) := by
  cases op with
  | interval h =>
      exact (occupation_joint_measurable N q (Fintype.card Copy) s).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_fst.snd))
  | boundary b => exact measurable_const

/-- Actual finite-segment law, with no conditioning on its stored success
flag. The equality is algebraic even before a completion theorem is invoked. -/
theorem actual_segment_exposure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (q : Copy → Base) (leafAge : Copy → ℝ)
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    ∀ᵐ z ∂actualSegmentLaw N r op s,
      forestPotential q leafAge (state z.2) (segmentMatrix N op s offset M z)
        (segmentOffset N op offset) =
      forestPotential q leafAge (state s) M offset + segmentOccupation N q op s z := by
  have hf : Measurable (fun z : SegmentRecord N sample =>
      forestPotential q leafAge (state z.2) (segmentMatrix N op s offset M z)
        (segmentOffset N op offset)) :=
    (forest_potential_joint_measurable N q leafAge).comp
      (((segment_matrix_measurable N op s offset M).prodMk measurable_const).prodMk measurable_snd)
  have hm : MeasurableSet {z : SegmentRecord N sample |
      forestPotential q leafAge (state z.2) (segmentMatrix N op s offset M z)
        (segmentOffset N op offset) =
      forestPotential q leafAge (state s) M offset + segmentOccupation N q op s z} :=
    measurableSet_eq_fun hf (measurable_const.add (segment_occupation_measurable N q op s))
  cases op with
  | interval h =>
      have ht := marked_trace_measurable N (Fintype.card Copy) s (h : ℝ)
      rw [actualSegmentLaw,actualMarkedTraceLaw,
        Measure.map_map (attach_endpoint_measurable N s) ht]
      apply (ae_map_iff ((attach_endpoint_measurable N s).comp ht).aemeasurable hm).mpr
      apply Filter.Eventually.of_forall
      intro c
      simpa only [segmentMatrix,segmentOffset,segmentOccupation,attachEndpoint,
        Function.comp_apply, actual_trace_occupation] using
        actual_literal_occupation_identity N q leafAge (Fintype.card Copy) s h offset c M
  | boundary b =>
      rw [actualSegmentLaw]
      apply (ae_map_iff (boundary_record_measurable N).aemeasurable hm).mpr
      simpa only [segmentMatrix,segmentOffset,segmentOccupation,boundaryRecord,add_zero] using
        actual_boundary_exposure N q leafAge M b s offset

def calendarTime (N : RootedBinary V E X) : List (ProgramStep N) → ℝ → ℝ
  | [],offset => offset
  | op::ops,offset => calendarTime N ops (segmentOffset N op offset)

def calendarOccupation (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) : (ops : List (ProgramStep N)) → Code N sample →
      (Fin ops.length → SegmentRecord N sample) → ℝ
  | [],_,_ => 0
  | op::ops,s,past => segmentOccupation N q op s (past 0) +
      calendarOccupation N q ops (past 0).2 (Fin.tail past)

lemma calendar_occupation_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (calendarOccupation N q ops s) := by
  induction ops generalizing s with
  | nil => exact measurable_const
  | cons op ops ih =>
      have hd : Measurable (fun z : Code N sample × (Fin ops.length → SegmentRecord N sample) =>
          calendarOccupation N q ops z.1 z.2) := measurable_from_prod_countable_right ih
      exact ((segment_occupation_measurable N q op s).comp (measurable_pi_apply 0)).add
        (hd.comp (((measurable_pi_apply 0).snd).prodMk
          (measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ))))

lemma calendar_exposure_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (leafAge : Copy → ℝ) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    MeasurableSet {past | forestPotential q leafAge (state (calendarEnd N ops s past))
      (calendarMatrix N ops s offset M past) (calendarTime N ops offset) =
      forestPotential q leafAge (state s) M offset + calendarOccupation N q ops s past} := by
  apply measurableSet_eq_fun
  · exact (forest_potential_joint_measurable N q leafAge).comp
      (((calendar_matrix_measurable N ops s offset M).prodMk measurable_const).prodMk
        (calendar_end_measurable N ops s))
  · exact measurable_const.add (calendar_occupation_measurable N q ops s)

/-- Telescope on the ACTUAL same-record calendar measure. Original ordered
boundaries, terminal fibres, offsets and matrices are retained. This is a
source-law occupation identity, not a desired exponential-polynomial
representation assumed as input. It asserts neither graph admission at
strict zero-length edges nor root-tail completion. -/
theorem actual_calendar_exposure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (q : Copy → Base) (leafAge : Copy → ℝ)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s,
      forestPotential q leafAge (state (calendarEnd N ops s past))
        (calendarMatrix N ops s offset M past) (calendarTime N ops offset) =
      forestPotential q leafAge (state s) M offset + calendarOccupation N q ops s past := by
  induction ops generalizing s offset M with
  | nil => exact Filter.Eventually.of_forall (fun _ => (add_zero _).symm)
  | cons op ops ih =>
      rw [actualCalendarTraceLaw,GProgram.G2.CalendarDecoration.ae_finsetSum_measure_iff]
      intro d hd
      letI := actual_segment_probability N r op s
      letI := actual_calendar_trace_probability N r ops d
      have hm := calendar_exposure_measurable N q leafAge (op::ops) s offset M
      have hmap := record_cons_measurable N (sample := sample) ops.length
      apply (ae_map_iff hmap.aemeasurable hm).mpr
      apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
      filter_upwards [ae_restrict_of_ae (actual_segment_exposure N r q leafAge op s offset M),
        ae_restrict_mem (measurableSet_eq_fun measurable_snd measurable_const)] with z hz he
      have he' : z.2 = d := he
      filter_upwards [ih d (segmentOffset N op offset) (segmentMatrix N op s offset M z)] with tail ht
      change forestPotential q leafAge (state (calendarEnd N ops z.2 tail))
        (calendarMatrix N ops z.2 (segmentOffset N op offset) (segmentMatrix N op s offset M z) tail)
        (calendarTime N ops (segmentOffset N op offset)) =
        forestPotential q leafAge (state s) M offset +
          (segmentOccupation N q op s z + calendarOccupation N q ops z.2 tail)
      rw [he',ht]
      rw [he'] at hz
      rw [hz]
      ring

/-- Finite-fuel success is imported from the original exponential-clock
provider at the ACTUAL copy-cap budget, not inferred from zeroing failures. -/
theorem actual_segment_success_ae (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) :
    ∀ᵐ z ∂actualSegmentLaw N r op s, z.1.1 = true := by
  have hm : MeasurableSet {z : SegmentRecord N sample | z.1.1 = true} :=
    measurableSet_eq_fun measurable_fst.fst measurable_const
  cases op with
  | interval h =>
      rw [actualSegmentLaw]
      apply (ae_map_iff (attach_endpoint_measurable N s).aemeasurable hm).mpr
      exact actual_marked_trace_success_ae N r (Fintype.card Copy) s h
        (Finset.card_le_univ s.val.live)
  | boundary b =>
      rw [actualSegmentLaw]
      apply (ae_map_iff (boundary_record_measurable N).aemeasurable hm).mpr
      exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Every stored finite-calendar success flag has full mass under the
original unnormalized terminal-fibre product construction. No conditioning
or resampling is introduced. Root-tail completion is a separate supplier. -/
theorem actual_calendar_success_ae (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s, ∀ i, (past i).1.1 = true := by
  induction ops generalizing s with
  | nil => exact Filter.Eventually.of_forall (fun _ i => Fin.elim0 i)
  | cons op ops ih =>
      rw [actualCalendarTraceLaw,GProgram.G2.CalendarDecoration.ae_finsetSum_measure_iff]
      intro d hd
      letI := actual_segment_probability N r op s
      letI := actual_calendar_trace_probability N r ops d
      have hm : MeasurableSet {past : Fin (op::ops).length → SegmentRecord N sample |
          ∀ i, (past i).1.1 = true} := by
        simpa only [Set.setOf_forall] using
          MeasurableSet.iInter (fun i : Fin (op::ops).length =>
            measurableSet_eq_fun (measurable_pi_apply i).fst.fst measurable_const)
      have hmap := record_cons_measurable N (sample := sample) ops.length
      apply (ae_map_iff hmap.aemeasurable hm).mpr
      apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
      filter_upwards [ae_restrict_of_ae (actual_segment_success_ae N r op s)] with z hz
      filter_upwards [ih d] with tail ht
      intro i
      exact Fin.cases hz ht i

#print axioms potential_decode_measurable
#print axioms forest_potential_joint_measurable
#print axioms actual_segment_exposure
#print axioms actual_calendar_exposure
#print axioms actual_segment_success_ae
#print axioms actual_calendar_success_ae
end ResearchCommons.MSCI.JC69CalendarOccupation
