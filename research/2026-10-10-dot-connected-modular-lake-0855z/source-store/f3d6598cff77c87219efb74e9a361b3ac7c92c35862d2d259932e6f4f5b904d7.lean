import G2SameClockContinuation
import G2SameClockPastFutureLaw

/-!
Finite earlier endpoint histories as measurable readouts of one later actual
marked trace. Contributor: dot (OpenAI), 6 October 2026. Inactive padding is
ignored before cutting at an inclusive horizon. No probability law is assumed.
-/
namespace GProgram.G2.EpochHistoryReadout
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceCuts
open GProgram.G2.SameClockContinuation
open GProgram.G2.SameClockPastFutureLaw
open UnifiedLean.Source.SourceLiteralClockEndpoint UnifiedLean.Source.SourcePoissonKernel
open scoped NNReal BigOperators
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

noncomputable def cutEndpoint (N : RootedBinary V E X) {sample : Copy → X} :
    (n : Nat) → ℝ → Code N sample → ClockTrace N sample n → Code N sample
  | 0,_,s,_ => s
  | n+1,u,s,z => cutEndpoint N n u
      (if (z 0).1 = true ∧ (z 0).2.1 ≤ u then (z 0).2.2 else s) (Fin.tail z)

lemma cut_endpoint_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (u : ℝ) :
    Measurable (fun z : Code N sample × ClockTrace N sample n => cutEndpoint N n u z.1 z.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      have hz : Measurable (fun z : Code N sample × ClockTrace N sample (n+1) => z.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have hA : MeasurableSet {z : Code N sample × ClockTrace N sample (n+1) |
          (z.2 0).1 = true ∧ (z.2 0).2.1 ≤ u} :=
        (measurableSet_eq_fun hz.fst measurable_const).inter
          (measurableSet_le hz.snd.fst measurable_const)
      have hs : Measurable (fun z : Code N sample × ClockTrace N sample (n+1) =>
          if (z.2 0).1 = true ∧ (z.2 0).2.1 ≤ u then (z.2 0).2.2 else z.1) :=
        Measurable.ite hA hz.snd.snd measurable_fst
      have ht : Measurable (fun z : Code N sample × ClockTrace N sample (n+1) => Fin.tail z.2) :=
        measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_snd)
      exact ih.comp (hs.prodMk ht)

/-- Equality of the finite-coordinate reader and the explicit active-list cut.
This holds for arbitrary record vectors, including arbitrary inactive padding. -/
theorem cut_endpoint_eq_record_fold (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (u : ℝ) (s : Code N sample) (z : ClockTrace N sample n) :
    cutEndpoint N n u s z = recordEndpoint s (cutRecords u (activeRecords z)) := by
  induction n generalizing s with
  | zero => simp [cutEndpoint,activeRecords,cutRecords,recordEndpoint]
  | succ n ih =>
      by_cases ha : (z 0).1 = true <;> by_cases hu : (z 0).2.1 ≤ u <;>
        simp [cutEndpoint,activeRecords,cutRecords,List.ofFn_succ,ha,hu,
          recordEndpoint,ih,Fin.tail_def]

/-- The actual compiler at the earlier horizon is recovered from the later
recorded trace on the SAME original clock vector, even on failed prefixes. -/
theorem actual_history_cut_readout (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (u t : ℝ) (s : Code N sample) (c : Choice N s → ℝ) (hut : u ≤ t) :
    cutEndpoint N n u s (literalMarkedTrace N n t s c).2 =
      traceEndpoint N n s (literalMarkedTrace N n u s c).2 := by
  rw [cut_endpoint_eq_record_fold,actual_trace_endpoint_fold]
  change recordEndpoint s (cutRecords u (activeTrace N n t s c)) =
    recordEndpoint s (activeTrace N n u s c)
  rw [activeTrace_horizon_restriction N n u t s c hut]

noncomputable def epochHistoryReadout (N : RootedBinary V E X) {sample : Copy → X}
    (n m : Nat) (s : Code N sample) (times : Fin m → ℝ)
    (z : Bool × ClockTrace N sample n) : Fin m → Code N sample :=
  fun i => cutEndpoint N n (times i) s z.2

lemma epoch_history_readout_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n m : Nat) (s : Code N sample) (times : Fin m → ℝ) :
    Measurable (epochHistoryReadout N n m s times) := by
  apply measurable_pi_lambda
  intro i
  exact (cut_endpoint_joint_measurable N n (times i)).comp
    (measurable_const.prodMk measurable_snd)

theorem actual_finite_history_readout (N : RootedBinary V E X) {sample : Copy → X}
    (n m : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (times : Fin m → ℝ) (ht : ∀ i, times i ≤ t) :
    epochHistoryReadout N n m s times (literalMarkedTrace N n t s c) =
      fun i => traceEndpoint N n s (literalMarkedTrace N n (times i) s c).2 := by
  funext i
  exact actual_history_cut_readout N n (times i) t s c (ht i)

#print axioms cut_endpoint_joint_measurable
#print axioms cut_endpoint_eq_record_fold
#print axioms actual_history_cut_readout
#print axioms epoch_history_readout_measurable
#print axioms actual_finite_history_readout
/-- Every finite earlier endpoint history shares the original source future
transition. These are unnormalized joint fibres, including null histories. -/
theorem actual_finite_history_future_source_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (m : Nat) (times : Fin m → ℝ) (t v : ℝ≥0) (ht : ∀ i, times i ≤ (t : ℝ)) :
    (currentPairClockMeasure N r s).map (fun c =>
      ((fun i => traceEndpoint N (Fintype.card Copy) s
        (literalMarkedTrace N (Fintype.card Copy) (times i) s c).2),
      literalClockEndpoint N (Fintype.card Copy) ((t : ℝ)+(v : ℝ)) s c)) =
      ∑ d : Code N sample,
        (((actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
          {h | decodedEndpoint N (Fintype.card Copy) s h = some d}).map
            (epochHistoryReadout N (Fintype.card Copy) m s times)).prod
          ((sourceTimeKernel N r v d).toMeasure.map some) := by
  letI := actual_marked_trace_probability N r (Fintype.card Copy) s t
  let H := epochHistoryReadout N (Fintype.card Copy) m s times
  have hH : Measurable H := epoch_history_readout_measurable N _ _ s times
  have hm : Measurable (Prod.map H (id : Option (Code N sample) → Option (Code N sample))) :=
    hH.prodMap measurable_id
  have hi : Measurable (fun c => (literalMarkedTrace N (Fintype.card Copy) (t : ℝ) s c,
      literalClockEndpoint N (Fintype.card Copy) ((t : ℝ)+(v : ℝ)) s c)) :=
    (marked_trace_measurable N _ s t).prodMk (literal_endpoint_measurable N _ s _)
  have h := congrArg (fun μ => μ.map (Prod.map H (id : Option (Code N sample) → Option (Code N sample))))
    (actual_same_clock_past_future_source_law N r s t v)
  rw [Measure.map_map hm hi,Measure.map_finset_sum' hm.aemeasurable] at h
  have he (d : Code N sample) :
      ((((actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
        {z | decodedEndpoint N (Fintype.card Copy) s z = some d}).prod
          ((sourceTimeKernel N r v d).toMeasure.map some)).map (Prod.map H id)) =
      (((actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
        {z | decodedEndpoint N (Fintype.card Copy) s z = some d}).map H).prod
          ((sourceTimeKernel N r v d).toMeasure.map some) := by
    rw [← Measure.map_prod_map _ _ hH measurable_id,Measure.map_id]
  simp_rw [he] at h
  have hr (c : Choice N s → ℝ) : H (literalMarkedTrace N (Fintype.card Copy) (t : ℝ) s c) =
      fun i => traceEndpoint N (Fintype.card Copy) s
        (literalMarkedTrace N (Fintype.card Copy) (times i) s c).2 :=
    actual_finite_history_readout N _ _ t s c times ht
  simpa only [Function.comp_def,Prod.map_apply,id_eq,hr] using h

#print axioms actual_finite_history_future_source_law

end GProgram.G2.EpochHistoryReadout
