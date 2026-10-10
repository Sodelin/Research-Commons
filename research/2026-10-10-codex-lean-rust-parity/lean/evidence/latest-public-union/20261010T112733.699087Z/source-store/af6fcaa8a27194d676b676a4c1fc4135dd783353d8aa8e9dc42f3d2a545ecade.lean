import G2CalendarPairSupport
import G2PairBirthThreshold
import G2AncestralPairSupport

/-!
Source support certificates for numerical whole-calendar age decoding.
Contributor: dot (OpenAI), 7 October 2026.
The certificate records actual clock-age bounds, order, pair persistence,
stored-state coherence and terminal pair support. It assumes no first-age
or matrix/path equality. Zero-mass endpoint fibres are kept unnormalized.
-/
namespace GProgram.G2.AncestralAgeCertificate
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceCuts
open GProgram.G2.EpochHistoryReadout GProgram.G2.PairBirthThreshold
open GProgram.G2.ActualCalendarTrace GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.CompleteDecoration GProgram.G2.FiniteAncestralTrace
open GProgram.G2.WholeMatrixAges GProgram.G2.CalendarPairSupport
open GProgram.G2.AncestralPairSupport GProgram.G2.ActualPairCoalescence
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

def ActiveAgeBounded (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (H : ℝ) (z : ClockTrace N sample n) : Prop :=
  ∀ i : Fin n, (z i).1 = true → (z i).2.1 ≤ H

noncomputable def SegmentAgeCertificate (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (z : SegmentRecord N sample) : Prop :=
  match op with
  | .interval h => ActiveAgeNonnegative N (Fintype.card Copy) z.1.2 ∧
      ActiveAgeOrdered N (Fintype.card Copy) z.1.2 ∧
      ActiveAgeBounded N (Fintype.card Copy) (h : ℝ) z.1.2
  | .boundary _ => True

noncomputable def CalendarAgeCertificate (N : RootedBinary V E X) {sample : Copy → X} :
    (ops : List (ProgramStep N)) → (Fin ops.length → SegmentRecord N sample) → Prop
  | [],_ => True
  | op::ops,past => SegmentAgeCertificate N op (past 0) ∧
      CalendarAgeCertificate N ops (Fin.tail past)

/-- The first conjunct is the exact stored-terminal identity used by the
preserved faithful-output consumer. Remaining fields are source support,
not a desired numerical observation law. -/
noncomputable def CompleteAgeCertificate (N : RootedBinary V E X) {sample : Copy → X}
    (P : Code N sample → Prop) (ops : List (ProgramStep N)) (s : Code N sample)
    (z : CompleteCalendarRecord N sample ops) : Prop :=
  z.1 = calendarEnd N ops s z.2.1 ∧
  (∀ x y : Copy, CompletePairCoherent N ops s z x y) ∧
  CalendarAgeCertificate N ops z.2.1 ∧
  ActiveAgeNonnegative N (Fintype.card Copy) z.2.2.2 ∧
  ActiveAgeOrdered N (Fintype.card Copy) z.2.2.2 ∧ P (completeEnd N ops z)

lemma active_nonnegative_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) : Measurable (ActiveAgeNonnegative N (sample := sample) n) := by
  apply Measurable.forall
  intro i
  exact (measurableSet_setOfPred.mp
    (measurableSet_eq_fun (measurable_pi_apply i).fst measurable_const)).imp
    (measurableSet_setOfPred.mp (measurableSet_le measurable_const (measurable_pi_apply i).snd.fst))

lemma active_ordered_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) : Measurable (ActiveAgeOrdered N (sample := sample) n) := by
  apply Measurable.forall
  intro i
  apply Measurable.forall
  intro j
  exact measurable_const.imp
    ((measurableSet_setOfPred.mp
      (measurableSet_eq_fun (measurable_pi_apply i).fst measurable_const)).imp
      ((measurableSet_setOfPred.mp
        (measurableSet_eq_fun (measurable_pi_apply j).fst measurable_const)).imp
        (measurableSet_setOfPred.mp (measurableSet_le
          (measurable_pi_apply i).snd.fst (measurable_pi_apply j).snd.fst))))

lemma active_bounded_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (H : ℝ) : Measurable (ActiveAgeBounded N (sample := sample) n H) := by
  apply Measurable.forall
  intro i
  exact (measurableSet_setOfPred.mp
    (measurableSet_eq_fun (measurable_pi_apply i).fst measurable_const)).imp
    (measurableSet_setOfPred.mp (measurableSet_le (measurable_pi_apply i).snd.fst measurable_const))

lemma segment_age_certificate_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) : Measurable (SegmentAgeCertificate N (sample := sample) op) := by
  cases op with
  | boundary _ => exact measurable_const
  | interval h =>
      exact ((active_nonnegative_measurable N _).comp measurable_fst.snd).and
        (((active_ordered_measurable N _).comp measurable_fst.snd).and
          ((active_bounded_measurable N _ (h : ℝ)).comp measurable_fst.snd))

lemma calendar_age_certificate_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) : Measurable (CalendarAgeCertificate N (sample := sample) ops) := by
  induction ops with
  | nil => exact measurable_const
  | cons op ops ih =>
      have ht : Measurable (fun past : Fin (op::ops).length → SegmentRecord N sample =>
          Fin.tail past) := measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)
      exact ((segment_age_certificate_measurable N (sample := sample) op).comp
        (measurable_pi_apply 0)).and (ih.comp ht)

lemma actual_literal_active_bounded (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (H : ℝ) (s : Code N sample) (c : Choice N s → ℝ) :
    ActiveAgeBounded N n H (literalMarkedTrace N n H s c).2 := by
  intro i hi
  have hmem : ((literalMarkedTrace N n H s c).2 i) ∈ activeTrace N n H s c := by
    change _ ∈ (List.ofFn (literalMarkedTrace N n H s c).2).filter (fun r => r.1)
    exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i,rfl⟩,hi⟩
  exact (activeTrace_mem_bounds N n H s c _ hmem).2

theorem actual_segment_age_certificate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) :
    ∀ᵐ z ∂actualSegmentLaw N r op s, SegmentAgeCertificate N op z := by
  cases op with
  | boundary _ => exact Filter.Eventually.of_forall (fun _ => True.intro)
  | interval h =>
      have ht := marked_trace_measurable N (Fintype.card Copy) s (h : ℝ)
      rw [actualSegmentLaw,actualMarkedTraceLaw,
        Measure.map_map (attach_endpoint_measurable N s) ht]
      apply (ae_map_iff ((attach_endpoint_measurable N s).comp ht).aemeasurable
        (segment_age_certificate_measurable N (.interval h)).setOf).mpr
      exact Filter.Eventually.of_forall (fun c =>
        ⟨actual_literal_active_nonnegative N _ (h : ℝ) s c,
          actual_literal_active_ordered N _ (h : ℝ) s c,
          actual_literal_active_bounded N _ (h : ℝ) s c⟩)

theorem actual_calendar_age_certificate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s, CalendarAgeCertificate N ops past := by
  induction ops generalizing s with
  | nil => exact Filter.Eventually.of_forall (fun _ => True.intro)
  | cons op ops ih =>
      rw [actualCalendarTraceLaw,ae_finsetSum_measure_iff]
      intro d _
      letI := actual_segment_probability N r op s
      letI := actual_calendar_trace_probability N r ops d
      have hm := (calendar_age_certificate_measurable N (sample := sample) (op::ops)).setOf
      have hmap := record_cons_measurable N (sample := sample) ops.length
      apply (ae_map_iff hmap.aemeasurable hm).mpr
      apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
      filter_upwards [ae_restrict_of_ae (actual_segment_age_certificate N r op s)] with z hz
      filter_upwards [ih d] with tail ht
      exact ⟨hz,ht⟩

lemma tail_age_certificate_measurable (N : RootedBinary V E X) {sample : Copy → X} :
    Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
      ActiveAgeNonnegative N _ z.2 ∧ ActiveAgeOrdered N _ z.2) :=
  ((active_nonnegative_measurable N _).comp measurable_snd).and
    ((active_ordered_measurable N _).comp measurable_snd)

theorem actual_tail_age_certificate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    ∀ᵐ z ∂completeAncestralTraceLaw N r s,
      ActiveAgeNonnegative N _ z.2 ∧ ActiveAgeOrdered N _ z.2 := by
  rw [completeAncestralTraceLaw]
  apply (ae_map_iff (complete_ancestral_trace_measurable N s).aemeasurable
    (tail_age_certificate_measurable N).setOf).mpr
  exact Filter.Eventually.of_forall (fun c =>
    ⟨actual_literal_active_nonnegative N _ (clockCover N s c : ℝ) s c,
      actual_literal_active_ordered N _ (clockCover N s c : ℝ) s c⟩)

theorem actual_completed_clock_ages (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s,
      CalendarAgeCertificate N ops z.2.1 ∧
      ActiveAgeNonnegative N _ z.2.2.2 ∧ ActiveAgeOrdered N _ z.2.2.2 := by
  rw [completeCalendarTraceLaw,ae_finsetSum_measure_iff]
  intro d _
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have hmap : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) := measurable_const.prodMk measurable_id
  have hm : Measurable (fun z : CompleteCalendarRecord N sample ops =>
      CalendarAgeCertificate N ops z.2.1 ∧
      ActiveAgeNonnegative N _ z.2.2.2 ∧ ActiveAgeOrdered N _ z.2.2.2) :=
    ((calendar_age_certificate_measurable N ops).comp measurable_snd.fst).and
      ((tail_age_certificate_measurable N).comp measurable_snd.snd)
  apply (ae_map_iff hmap.aemeasurable hm.setOf).mpr
  apply (Measure.ae_prod_iff_ae_ae (hm.setOf.preimage hmap)).mpr
  filter_upwards [ae_restrict_of_ae (actual_calendar_age_certificate N r ops s)] with past hp
  filter_upwards [actual_tail_age_certificate N r d] with tail ht
  exact ⟨hp,ht⟩

/-- Only positive original endpoint fibres require ancestral-root support.
A null fibre vanishes as a measure, without dividing by its mass. -/
theorem actual_complete_pairs_joined (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (hroot : ∀ d, sourceProgram N r ops s d ≠ 0 → AncestralRoot N d) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s, AllPairsJoined N (completeEnd N ops z) := by
  rw [completeCalendarTraceLaw,ae_finsetSum_measure_iff]
  intro d _
  by_cases hd : sourceProgram N r ops s d = 0
  · have hz : (actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d} = 0 :=
      Measure.restrict_eq_zero.mpr (by rw [calendar_end_fibre_mass,hd])
    simp [hz]
  · letI := actual_calendar_trace_probability N r ops s
    letI := complete_ancestral_trace_probability N r d
    have hmap : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
        (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) := measurable_const.prodMk measurable_id
    have hm : MeasurableSet {z : CompleteCalendarRecord N sample ops |
        AllPairsJoined N (completeEnd N ops z)} :=
      ((measurable_of_countable (fun d : Code N sample => AllPairsJoined N d)).comp
        (complete_end_measurable N (sample := sample) ops)).setOf
    apply (ae_map_iff hmap.aemeasurable hm).mpr
    apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
    exact Filter.Eventually.of_forall (fun _ => actual_ancestral_pairs_joined_ae N r d (hroot d hd))

/-- Exact preserved consumer interface: selected pairs receive an actual
complete-record certificate, including the diagonal and empty-panel cases. -/
theorem actual_complete_pair_certificate (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) {x y : Copy} (hx : x ∈ keep) (hy : y ∈ keep)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (hroot : ∀ d, sourceProgram N r ops s d ≠ 0 → AncestralRoot N d) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s,
      CompleteAgeCertificate N (fun d => sameBlock (selectedView (state d) keep) x y) ops s z := by
  have hc : ∀ᵐ z ∂completeCalendarTraceLaw N r ops s,
      ∀ u v : Copy, CompletePairCoherent N ops s z u v :=
    ae_all_iff.mpr (fun u => ae_all_iff.mpr (fun v => actual_complete_pair_coherent N r ops s u v))
  filter_upwards [hc,actual_completed_clock_ages N r ops s,
    actual_complete_pairs_joined N r ops s hroot] with z hz ha hp
  exact ⟨(hz x y).2.1,hz,ha.1,ha.2.1,ha.2.2,
    (selected_same_block (state (completeEnd N ops z)) (completeEnd N ops z).property.forest keep hx hy).mpr (hp x y)⟩

#print axioms active_nonnegative_measurable
#print axioms active_ordered_measurable
#print axioms active_bounded_measurable
#print axioms calendar_age_certificate_measurable
#print axioms actual_literal_active_bounded
#print axioms actual_segment_age_certificate
#print axioms actual_calendar_age_certificate
#print axioms actual_tail_age_certificate
#print axioms actual_completed_clock_ages
#print axioms actual_complete_pairs_joined
#print axioms actual_complete_pair_certificate
end GProgram.G2.AncestralAgeCertificate
