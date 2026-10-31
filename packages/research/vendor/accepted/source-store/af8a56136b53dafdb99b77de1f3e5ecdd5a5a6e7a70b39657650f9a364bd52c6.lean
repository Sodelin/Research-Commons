import G2ActualSegmentPathLaw
import G2FiniteFibreTransport
import G2CalendarHistoryBinding

/-!
Joint paths and terminal states of the actual finite calendar.
Contributor: dot (OpenAI), 6 October 2026. Each observed segment is read from
the original record. The calendar induction uses unnormalized actual terminal
fibres and the proved one-segment observation law. Completed ancestral joining
and faithful age decoding remain separate.
-/
namespace GProgram.G2.CalendarPathProjection
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.ActualSegmentPathLaw GProgram.G2.FiniteFibreTransport
open GProgram.G2.EpochPathProjection
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [MeasurableSpace Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.EpochPathProjection.joinedIndexMeasurable

def observedCons (n : Nat) (z : SegmentObservation Q × (Fin n → SegmentObservation Q)) :
    Fin (n+1) → SegmentObservation Q := Fin.cons z.1 z.2

lemma observed_cons_measurable (n : Nat) : Measurable (observedCons (Q := Q) n) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

noncomputable def observeCalendarSegments (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) : (ops : List (ProgramStep N)) → Code N sample →
      (Fin ops.length → SegmentRecord N sample) → (Fin ops.length → SegmentObservation Q)
  | [],_,_ => fun i => Fin.elim0 i
  | op::ops,s,z => Fin.cons (observedSegment N f op s (z 0))
      (observeCalendarSegments N f ops (z 0).2 (Fin.tail z))

lemma observe_calendar_segments_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (observeCalendarSegments N f ops s) := by
  induction ops generalizing s with
  | nil =>
      apply measurable_pi_lambda
      intro i
      exact Fin.elim0 i
  | cons op ops ih =>
      have hm : Measurable (fun z : Code N sample × (Fin ops.length → SegmentRecord N sample) =>
          observeCalendarSegments N f ops z.1 z.2) := measurable_from_prod_countable_right ih
      have ht : Measurable (Fin.tail : (Fin (op::ops).length → SegmentRecord N sample) →
          (Fin ops.length → SegmentRecord N sample)) :=
        measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)
      apply measurable_pi_lambda
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (observed_segment_measurable N f op s).comp (measurable_pi_apply 0)
      · exact (measurable_pi_apply j).comp
          (hm.comp (((measurable_pi_apply 0).snd).prodMk ht))

noncomputable def observedCalendarEnd (N : RootedBinary V E X) :
    (ops : List (ProgramStep N)) → Q → (Fin ops.length → SegmentObservation Q) → Q
  | [],q,_ => q
  | _::ops,_,z => observedCalendarEnd N ops (z 0).2 (Fin.tail z)

theorem observe_calendar_terminal_agrees (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample)
    (z : Fin ops.length → SegmentRecord N sample) :
    observedCalendarEnd N ops (f s) (observeCalendarSegments N f ops s z) =
      f (calendarEnd N ops s z) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      cases op <;> simpa only [observedCalendarEnd,observeCalendarSegments,
        Fin.cons_zero,Fin.tail_cons,observedSegment,constantObservation,calendarEnd] using ih (z 0).2 (Fin.tail z)

variable [Fintype Q] [MeasurableSingletonClass Q]

noncomputable def coarseCalendarLaw (N : RootedBinary V E X)
    (K : ProgramStep N → Q → Measure (SegmentObservation Q)) :
    (ops : List (ProgramStep N)) → Q → Measure (Fin ops.length → SegmentObservation Q)
  | [],_ => Measure.dirac (fun i => Fin.elim0 i)
  | op::ops,q => ∑ d : Q,
      (((K op q).restrict {z | z.2 = d}).prod (coarseCalendarLaw N K ops d)).map
        (observedCons ops.length)

lemma finite_terminal_mass_sum (μ : Measure (SegmentObservation Q)) [IsProbabilityMeasure μ] :
    (∑ d : Q, μ {z | z.2 = d}) = 1 := by
  have h := congrArg (fun η : Measure (SegmentObservation Q) => η univ)
    (finite_fibre_decomposition μ Prod.snd measurable_snd)
  rw [show μ univ = 1 from measure_univ,Measure.finsetSum_apply Finset.univ _ univ] at h
  simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter] using h.symm

theorem coarse_calendar_probability (N : RootedBinary V E X)
    (K : ProgramStep N → Q → Measure (SegmentObservation Q))
    (hK : ∀ op q, IsProbabilityMeasure (K op q))
    (ops : List (ProgramStep N)) (q : Q) : IsProbabilityMeasure (coarseCalendarLaw N K ops q) := by
  induction ops generalizing q with
  | nil => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | cons op ops ih =>
      letI := hK op q
      have hm (d : Q) :
          (((((K op q).restrict {z | z.2 = d}).prod (coarseCalendarLaw N K ops d)).map
            (observedCons ops.length)) univ) = K op q {z | z.2 = d} := by
        letI := ih d
        have ht : (coarseCalendarLaw N K ops d) univ = 1 := measure_univ
        rw [Measure.map_apply (observed_cons_measurable _) MeasurableSet.univ,
          preimage_univ,← univ_prod_univ,Measure.prod_prod,ht,mul_one,
          Measure.restrict_apply MeasurableSet.univ,univ_inter]
      constructor
      calc
        (coarseCalendarLaw N K (op::ops) q) univ =
            ∑ d : Q, K op q {z | z.2 = d} := by
          simp only [coarseCalendarLaw,List.length_cons]
          rw [Measure.finsetSum_apply (Finset.univ : Finset Q)
              (fun d : Q => (((K op q).restrict {z | z.2 = d}).prod
                (coarseCalendarLaw N K ops d)).map (observedCons ops.length))
              (Set.univ : Set (Fin (ops.length+1) → SegmentObservation Q))]
          exact Finset.sum_congr rfl (fun d _ => hm d)
        _ = 1 := finite_terminal_mass_sum (K op q)

/-- No measurability of equality between arbitrary uncountable-time paths is
used here. The measurable event is the finite original endpoint fibre. -/
theorem calendar_branch_segments_map (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (f : Code N sample → Q)
    (op : ProgramStep N) (ops : List (ProgramStep N)) (s d : Code N sample) :
    (((((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
      (actualCalendarTraceLaw N r ops d)).map (recordCons N ops.length)).map
        (observeCalendarSegments N f (op::ops) s)) =
      ((((actualSegmentLaw N r op s).restrict {z | z.2 = d}).map (observedSegment N f op s)).prod
        ((actualCalendarTraceLaw N r ops d).map (observeCalendarSegments N f ops d))).map
          (observedCons ops.length) := by
  letI := actual_segment_probability N r op s
  letI := actual_calendar_trace_probability N r ops d
  have hA : MeasurableSet {z : SegmentRecord N sample | z.2 = d} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have hfirst : ∀ᵐ z ∂((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
      (actualCalendarTraceLaw N r ops d), z.1.2 = d := by
    have hm : MeasurableSet {z : SegmentRecord N sample ×
        (Fin ops.length → SegmentRecord N sample) | z.1.2 = d} :=
      measurableSet_eq_fun measurable_fst.snd measurable_const
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [ae_restrict_mem hA] with z hz
    exact Filter.Eventually.of_forall (fun _ => hz)
  have he : (observeCalendarSegments N f (op::ops) s ∘ recordCons N ops.length) =ᵐ[
      ((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
        (actualCalendarTraceLaw N r ops d)]
      (observedCons ops.length ∘ Prod.map (observedSegment N f op s)
        (observeCalendarSegments N f ops d)) := by
    filter_upwards [hfirst] with z hz
    simp only [Function.comp_apply,recordCons,observeCalendarSegments,Fin.cons_zero,
      Fin.tail_cons,Prod.map_apply,observedCons]
    rw [hz]
    rfl
  rw [Measure.map_map (observe_calendar_segments_measurable N f _ s)
      (record_cons_measurable N _),Measure.map_congr he,
    ← Measure.map_map (observed_cons_measurable _)
      ((observed_segment_measurable N f op s).prodMap (observe_calendar_segments_measurable N f ops d)),
    ← Measure.map_prod_map _ _ (observed_segment_measurable N f op s)
      (observe_calendar_segments_measurable N f ops d)]

/-- Abstract row transport is used only as an induction lemma. Both actual
full/small source applications below discharge its one-segment premise. -/
theorem actual_calendar_segments_common (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (f : Code N sample → Q)
    (K : ProgramStep N → Q → Measure (SegmentObservation Q))
    (hK : ∀ op q, IsProbabilityMeasure (K op q))
    (hrow : ∀ op s, (actualSegmentLaw N r op s).map (observedSegment N f op s) = K op (f s))
    (ops : List (ProgramStep N)) (s : Code N sample) :
    (actualCalendarTraceLaw N r ops s).map (observeCalendarSegments N f ops s) =
      coarseCalendarLaw N K ops (f s) := by
  induction ops generalizing s with
  | nil =>
      rw [actualCalendarTraceLaw,Measure.map_dirac' (observe_calendar_segments_measurable N f [] s)]
      rfl
  | cons op ops ih =>
      letI := actual_segment_probability N r op s
      let ν : Q → Measure (Fin ops.length → SegmentObservation Q) := coarseCalendarLaw N K ops
      letI : ∀ q, IsProbabilityMeasure (ν q) := fun q => coarse_calendar_probability N K hK ops q
      letI : ∀ q, SFinite (ν q) := fun q => inferInstance
      have hc : ∀ z : SegmentRecord N sample, (observedSegment N f op s z).2 = f z.2 := by
        intro z
        cases op <;> rfl
      have h := finite_endpoint_fibre_product_regroup_map (actualSegmentLaw N r op s)
        Prod.snd (observedSegment N f op s) f Prod.snd measurable_snd
        (observed_segment_measurable N f op s) measurable_snd hc ν (K op (f s))
        (hrow op s) (observedCons ops.length) (observed_cons_measurable _)
      rw [actualCalendarTraceLaw,
        Measure.map_finset_sum' (observe_calendar_segments_measurable N f (op::ops) s).aemeasurable]
      simp_rw [calendar_branch_segments_map,ih]
      exact h

lemma common_segment_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (q : JoinedIndex N sample keep) :
    IsProbabilityMeasure (commonObservedSegmentLaw N r keep op q) := by
  exact joined_observed_segment_probability N r keep op (joinedRepresentative N keep q)

/-- Exact full/small equality of all observed calendar segment paths together
with their terminal states, retaining every original operation and register. -/
theorem actual_cross_carrier_calendar_paths (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N sample)
    (d : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state d) Finset.univ)) :
    (actualCalendarTraceLaw N r ops s).map
      (observeCalendarSegments N (fun z => joinedProjection N keep (.inl z)) ops s) =
    (actualCalendarTraceLaw N r ops d).map
      (observeCalendarSegments N (fun z => joinedProjection N keep (.inr z)) ops d) := by
  have hf (op : ProgramStep N) (s : Code N sample) :=
    joined_observed_segment_common N r keep op (.inl s)
  have hg (op : ProgramStep N) (s : Code N (selectedSample sample keep)) :=
    joined_observed_segment_common N r keep op (.inr s)
  rw [actual_calendar_segments_common N r _ (commonObservedSegmentLaw N r keep)
      (common_segment_probability N r keep) hf,
    actual_calendar_segments_common N r _ (commonObservedSegmentLaw N r keep)
      (common_segment_probability N r keep) hg]
  have he : joinedProjection N keep (.inl s) = joinedProjection N keep (.inr d) := Subtype.ext hs
  rw [he]

#print axioms observed_cons_measurable
#print axioms observe_calendar_segments_measurable
#print axioms observe_calendar_terminal_agrees
#print axioms finite_terminal_mass_sum
#print axioms coarse_calendar_probability
#print axioms calendar_branch_segments_map
#print axioms actual_calendar_segments_common
#print axioms common_segment_probability
#print axioms actual_cross_carrier_calendar_paths
end GProgram.G2.CalendarPathProjection
