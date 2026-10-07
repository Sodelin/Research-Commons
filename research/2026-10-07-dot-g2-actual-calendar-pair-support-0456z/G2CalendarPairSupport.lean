import G2WholeMatrixAges
import G2ActualPairCoalescence

/-!
Actual source support for whole-calendar pair coherence.
Contributor: dot (OpenAI), 7 October 2026.
All fibres remain unnormalized, including null fibres and empty carriers.
-/
namespace GProgram.G2.CalendarPairSupport
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceCuts
open GProgram.G2.SameClockContinuation GProgram.G2.PairBirthFold
open GProgram.G2.ActualCalendarTrace GProgram.G2.CalendarDecoration
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompleteDecoration
open GProgram.G2.FiniteAncestralTrace GProgram.G2.WholeMatrixAges
open GProgram.G2.ActualPairCoalescence
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

lemma carried_endpoint_joint_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) :
    Measurable (fun z : Code N sample × ClockTrace N sample n =>
      recordEndpoint z.1 (activeRecords z.2)) := by
  classical
  induction n with
  | zero => simpa [activeRecords,recordEndpoint] using
      (measurable_fst : Measurable (fun z : Code N sample × ClockTrace N sample 0 => z.1))
  | succ n ih =>
      have hh : Measurable (fun z : Code N sample × ClockTrace N sample (n+1) => z.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have ht : Measurable (fun z : Code N sample × ClockTrace N sample (n+1) => Fin.tail z.2) :=
        measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_snd)
      have hA := measurableSet_eq_fun hh.fst (measurable_const (a := true))
      have h : Measurable (fun z : Code N sample × ClockTrace N sample (n+1) =>
          if (z.2 0).1 = true then recordEndpoint (z.2 0).2.2 (activeRecords (Fin.tail z.2))
          else recordEndpoint z.1 (activeRecords (Fin.tail z.2))) :=
        Measurable.ite hA (ih.comp (hh.snd.snd.prodMk ht))
          (ih.comp (measurable_fst.prodMk ht))
      simpa only [carried_endpoint_succ,Fin.tail_def] using h

lemma pair_monotone_joint_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (x y : Copy) :
    Measurable (fun z : Code N sample × ClockTrace N sample n =>
      PairTraceMonotone N n z.1 z.2 x y) := by
  classical
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hh : Measurable (fun z : Code N sample × ClockTrace N sample (n+1) => z.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have ht : Measurable (fun z : Code N sample × ClockTrace N sample (n+1) => Fin.tail z.2) :=
        measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_snd)
      have hp : Measurable (fun q : Code N sample × Code N sample =>
          (state q.1).ancestor x = (state q.1).ancestor y →
            (state q.2).ancestor x = (state q.2).ancestor y) := measurable_of_countable _
      have h : Measurable (fun z : Code N sample × ClockTrace N sample (n+1) =>
          if (z.2 0).1 = true then
            ((state z.1).ancestor x = (state z.1).ancestor y →
              (state (z.2 0).2.2).ancestor x = (state (z.2 0).2.2).ancestor y) ∧
              PairTraceMonotone N n (z.2 0).2.2 (Fin.tail z.2) x y
          else PairTraceMonotone N n z.1 (Fin.tail z.2) x y) :=
        Measurable.ite (measurableSet_eq_fun hh.fst (measurable_const (a := true)))
          ((hp.comp (measurable_fst.prodMk hh.snd.snd)).and
            (ih.comp (hh.snd.snd.prodMk ht))) (ih.comp (measurable_fst.prodMk ht))
      simpa only [PairTraceMonotone,Fin.tail_def] using h

lemma segment_pair_coherent_joint_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (op : ProgramStep N) (x y : Copy) :
    Measurable (fun z : Code N sample × SegmentRecord N sample =>
      SegmentPairCoherent N op z.1 z.2 x y) := by
  cases op with
  | interval h =>
      have hz : Measurable (fun z : Code N sample × SegmentRecord N sample => (z.1,z.2.1.2)) :=
        measurable_fst.prodMk measurable_snd.fst.snd
      exact ((pair_monotone_joint_measurable N _ x y).comp hz).and
        (measurableSet_setOfPred.mp (measurableSet_eq_fun measurable_snd.snd
          ((carried_endpoint_joint_measurable N _).comp hz)))
  | boundary b =>
      have hp : Measurable (fun q : Code N sample × Code N sample =>
          ((state q.1).ancestor x = (state q.1).ancestor y ↔
            (state q.2).ancestor x = (state q.2).ancestor y)) := measurable_of_countable _
      exact hp.comp (measurable_fst.prodMk measurable_snd.snd)

lemma calendar_pair_coherent_joint_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (ops : List (ProgramStep N)) (x y : Copy) :
    Measurable (fun z : Code N sample × (Fin ops.length → SegmentRecord N sample) =>
      CalendarPairCoherent N ops z.1 z.2 x y) := by
  induction ops with
  | nil => exact measurable_const
  | cons op ops ih =>
      have hh : Measurable (fun z : Code N sample × (Fin (op::ops).length → SegmentRecord N sample) => z.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have ht : Measurable (fun z : Code N sample × (Fin (op::ops).length → SegmentRecord N sample) => Fin.tail z.2) :=
        measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_snd)
      exact ((segment_pair_coherent_joint_measurable N op x y).comp
        (measurable_fst.prodMk hh)).and (ih.comp (hh.snd.prodMk ht))

/-- The unchanged original boundary law preserves the entire genealogy,
which supplies both directions of pair ancestry equivalence. -/
lemma original_boundary_pair_support (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s d : Code N sample) (x y : Copy)
    (hd : d ∈ (boundaryKernel N b s).support) :
    ((state s).ancestor x = (state s).ancestor y ↔
      (state d).ancestor x = (state d).ancestor y) := by
  let f := fun q : Code N sample => (selectedView (state q) Finset.univ).genealogy
  have hmem : f d ∈ ((boundaryKernel N b s).map f).support :=
    (PMF.mem_support_map_iff f (boundaryKernel N b s) (f d)).mpr ⟨d,hd,rfl⟩
  have law := boundary_genealogy_law N b s Finset.univ
  change (boundaryKernel N b s).map f = PMF.pure (f s) at law
  rw [law] at hmem
  have he : f d = f s := (PMF.mem_support_pure_iff _ _).mp hmem
  rw [← selected_same_block (state s) s.property.forest Finset.univ
      (Finset.mem_univ x) (Finset.mem_univ y),
    ← selected_same_block (state d) d.property.forest Finset.univ
      (Finset.mem_univ x) (Finset.mem_univ y)]
  change y ∈ Genealogy.optionLeaves (f s x) ↔ y ∈ Genealogy.optionLeaves (f d x)
  rw [he]

theorem actual_boundary_pair_coherent (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s : Code N sample) (x y : Copy) :
    ∀ᵐ d ∂(boundaryKernel N b s).toMeasure,
      ((state s).ancestor x = (state s).ancestor y ↔
        (state d).ancestor x = (state d).ancestor y) := by
  have hm : Measurable (fun d : Code N sample =>
      ((state s).ancestor x = (state s).ancestor y ↔
        (state d).ancestor x = (state d).ancestor y)) := measurable_of_countable _
  rw [ae_iff_prob_eq_one hm,PMF.toMeasure_apply_eq_one_iff _ hm.setOf]
  exact fun d hd => original_boundary_pair_support N b s d x y hd

theorem actual_segment_pair_coherent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) (x y : Copy) :
    ∀ᵐ z ∂actualSegmentLaw N r op s, SegmentPairCoherent N op s z x y := by
  have hm : MeasurableSet {z : SegmentRecord N sample | SegmentPairCoherent N op s z x y} :=
    ((segment_pair_coherent_joint_measurable N (sample := sample) op x y).comp
      ((measurable_const (a := s)).prodMk measurable_id)).setOf
  cases op with
  | interval h =>
      have ht := marked_trace_measurable N (Fintype.card Copy) s (h : ℝ)
      rw [actualSegmentLaw,actualMarkedTraceLaw,
        Measure.map_map (attach_endpoint_measurable N s) ht]
      apply (ae_map_iff ((attach_endpoint_measurable N s).comp ht).aemeasurable hm).mpr
      apply Filter.Eventually.of_forall
      intro c
      exact ⟨actual_literal_pair_monotone N _ (h : ℝ) s c x y,
        actual_trace_endpoint_fold N _ (h : ℝ) s c⟩
  | boundary b =>
      rw [actualSegmentLaw]
      apply (ae_map_iff (boundary_record_measurable N).aemeasurable hm).mpr
      exact actual_boundary_pair_coherent N b s x y

theorem actual_calendar_pair_coherent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (x y : Copy) :
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s, CalendarPairCoherent N ops s past x y := by
  induction ops generalizing s with
  | nil => exact Filter.Eventually.of_forall (fun _ => True.intro)
  | cons op ops ih =>
      rw [actualCalendarTraceLaw,ae_finsetSum_measure_iff]
      intro d _
      letI := actual_segment_probability N r op s
      letI := actual_calendar_trace_probability N r ops d
      have hm : MeasurableSet {past : Fin (op::ops).length → SegmentRecord N sample |
          CalendarPairCoherent N (op::ops) s past x y} :=
        ((calendar_pair_coherent_joint_measurable N (sample := sample) (op::ops) x y).comp
          ((measurable_const (a := s)).prodMk measurable_id)).setOf
      have hmap := record_cons_measurable N (sample := sample) ops.length
      apply (ae_map_iff hmap.aemeasurable hm).mpr
      apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
      filter_upwards [ae_restrict_of_ae (actual_segment_pair_coherent N r op s x y),
        ae_restrict_mem (measurableSet_eq_fun measurable_snd measurable_const)] with z hz he
      filter_upwards [ih d] with tail ht
      change SegmentPairCoherent N op s z x y ∧ CalendarPairCoherent N ops z.2 tail x y
      exact ⟨hz,by simpa only [show z.2 = d from he] using ht⟩

lemma tail_pair_coherent_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (x y : Copy) :
    Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
      PairTraceMonotone N (Fintype.card Copy) s z.2 x y ∧
      traceEndpoint N (Fintype.card Copy) s z.2 = recordEndpoint s (activeRecords z.2)) := by
  have hp : Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) => (s,z.2)) :=
    measurable_const.prodMk measurable_snd
  exact ((pair_monotone_joint_measurable N _ x y).comp hp).and
    (measurableSet_setOfPred.mp (measurableSet_eq_fun
      ((trace_end_joint_measurable N _).comp hp) ((carried_endpoint_joint_measurable N _).comp hp)))

theorem actual_tail_pair_coherent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (x y : Copy) :
    ∀ᵐ z ∂completeAncestralTraceLaw N r s,
      PairTraceMonotone N (Fintype.card Copy) s z.2 x y ∧
      traceEndpoint N (Fintype.card Copy) s z.2 = recordEndpoint s (activeRecords z.2) := by
  rw [completeAncestralTraceLaw]
  apply (ae_map_iff (complete_ancestral_trace_measurable N s).aemeasurable
    (tail_pair_coherent_measurable N s x y).setOf).mpr
  exact Filter.Eventually.of_forall (fun c =>
    ⟨actual_literal_pair_monotone N _ (clockCover N s c : ℝ) s c x y,
      actual_trace_endpoint_fold N _ (clockCover N s c : ℝ) s c⟩)

lemma complete_pair_coherent_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (x y : Copy) :
    Measurable (CompletePairCoherent N ops s (sample := sample) · x y) := by
  have hp : Measurable (fun z : CompleteCalendarRecord N sample ops => (z.1,z.2.2.2)) :=
    measurable_fst.prodMk measurable_snd.snd.snd
  exact ((calendar_pair_coherent_joint_measurable N ops x y).comp
    (measurable_const.prodMk measurable_snd.fst)).and
    ((measurableSet_setOfPred.mp (measurableSet_eq_fun measurable_fst
      ((calendar_end_measurable N ops s).comp measurable_snd.fst))).and
      (((pair_monotone_joint_measurable N _ x y).comp hp).and
        (measurableSet_setOfPred.mp (measurableSet_eq_fun
          ((trace_end_joint_measurable N _).comp hp) ((carried_endpoint_joint_measurable N _).comp hp)))))

/-- The structural premises of the deterministic whole-matrix bridge hold
under the actual original law; no positive-mass fibre is normalized. -/
theorem actual_complete_pair_coherent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) (x y : Copy) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s, CompletePairCoherent N ops s z x y := by
  rw [completeCalendarTraceLaw,ae_finsetSum_measure_iff]
  intro d _
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have hmap : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) := measurable_const.prodMk measurable_id
  have hm := (complete_pair_coherent_measurable N ops s x y).setOf
  apply (ae_map_iff hmap.aemeasurable hm).mpr
  apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
  filter_upwards [ae_restrict_of_ae (actual_calendar_pair_coherent N r ops s x y),
    ae_restrict_mem (measurableSet_eq_fun (calendar_end_measurable N ops s) measurable_const)] with past hp he
  filter_upwards [actual_tail_pair_coherent N r d x y] with tail ht
  exact ⟨hp,(show calendarEnd N ops s past = d from he).symm,ht.1,ht.2⟩

theorem actual_complete_first_birth_matrix (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s,
      completeMatrix N ops s offset M z =
        fun x y => (completeFirstPairBirth N ops s offset z x y).getD (M x y) := by
  have hc : ∀ᵐ z ∂completeCalendarTraceLaw N r ops s,
      ∀ x y : Copy, CompletePairCoherent N ops s z x y :=
    ae_all_iff.mpr (fun x => ae_all_iff.mpr (fun y => actual_complete_pair_coherent N r ops s x y))
  filter_upwards [hc] with z hz
  exact complete_matrix_eq_first_birth_matrix N ops s offset M z hz

#print axioms carried_endpoint_joint_measurable
#print axioms pair_monotone_joint_measurable
#print axioms segment_pair_coherent_joint_measurable
#print axioms calendar_pair_coherent_joint_measurable
#print axioms original_boundary_pair_support
#print axioms actual_boundary_pair_coherent
#print axioms actual_segment_pair_coherent
#print axioms actual_calendar_pair_coherent
#print axioms actual_tail_pair_coherent
#print axioms complete_pair_coherent_measurable
#print axioms actual_complete_pair_coherent
#print axioms actual_complete_first_birth_matrix
end GProgram.G2.CalendarPairSupport
