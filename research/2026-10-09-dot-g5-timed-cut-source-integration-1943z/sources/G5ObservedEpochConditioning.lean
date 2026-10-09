import G5ActualNoEventEpoch
import G5ActualNoMergerReadout
import G2ActualSegmentPathLaw

/-!
# Genealogy-observed conditioning on the original epoch clock space
Contributor: dot, 2026-10-09. Candidate until separately compiled and reviewed.
The conditioning event reads ancestry discreteness, not the latent clock catalogue.
The equivalence to no-first-merger is derived on the original clock measure.
-/
namespace GProgram.G5.ObservedEpochConditioning
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceLiteralClockEndpoint
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteAncestralPath GProgram.G2.EpochHistoryReadout
open GProgram.G5.ActualNoEventEpoch GProgram.G5.ActualNoMergerReadout
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.HistoryResidualAttachment.current_clock_probability

noncomputable def observedSurvival (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : ℝ≥0) : Set (Choice N s → ℝ) :=
  {c | discreteReadout N (literalEpochPath N s c t) = true}

lemma epoch_endpoint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : ℝ≥0) : Measurable (fun c => literalEpochPath N s c t) :=
  (measurable_pi_apply t).comp (literal_epoch_path_measurable N s)

lemma observed_survival_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : ℝ≥0) : MeasurableSet (observedSurvival N s t) :=
  measurableSet_eq_fun ((measurable_of_countable (discreteReadout N)).comp
    (epoch_endpoint_measurable N s t)) measurable_const

lemma actual_epoch_endpoint_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) :
    (currentPairClockMeasure N r s).map (fun c => literalEpochPath N s c t) =
      (sourceTimeKernel N r t s).toMeasure := by
  have h := actual_trace_endpoint_source_law N r s t
  have hf : Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
      traceEndpoint N (Fintype.card Copy) s z.2) :=
    (trace_endpoint_measurable N (Fintype.card Copy) s).comp measurable_snd
  rw [actualMarkedTraceLaw, Measure.map_map hf
    (marked_trace_measurable N (Fintype.card Copy) s t)] at h
  exact h

lemma no_first_subset_observed (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : ℝ≥0) (hs : Function.Injective (state s).ancestor) :
    currentNoFirstMerger N s t ⊆ observedSurvival N s t := by
  intro c hc
  have hc' : ∀ p : Choice N s, (t : ℝ) < c p := by
    simpa [currentNoFirstMerger, Set.mem_pi] using hc
  change discreteReadout N (literalEpochPath N s c t) = true
  have he (n : Nat) : traceEndpoint N n s (literalMarkedTrace N n (t : ℝ) s c).2 = s := by
    cases n with
    | zero => rfl
    | succ n => simp [literalMarkedTrace, hc']
  change discreteReadout N (traceEndpoint N (Fintype.card Copy) s
    (literalMarkedTrace N (Fintype.card Copy) (t : ℝ) s c).2) = true
  rw [he]
  simp [discreteReadout, hs]

lemma actual_observed_survival_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) :
    currentPairClockMeasure N r s (observedSurvival N s t) =
      ((sourceTimeKernel N r t s).map (discreteReadout N)) true := by
  have h := congrArg (fun m : Measure (Code N sample) => m.map (discreteReadout N))
    (actual_epoch_endpoint_law N r s t)
  rw [Measure.map_map (measurable_of_countable _) (epoch_endpoint_measurable N s t),
    PMF.toMeasure_map _ _ (measurable_of_countable _)] at h
  have he := congrArg (fun m : Measure Bool => m {true}) h
  rw [Measure.map_apply ((measurable_of_countable (discreteReadout N)).comp
      (epoch_endpoint_measurable N s t)) (MeasurableSet.singleton true),
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton true)] at he
  exact he

/-- Equality of observable and clock events is proved on the SAME original
clock measure. No independence or conditional-law assertion is a premise. -/
theorem actual_observed_survival_ae (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0)
    (hs : Function.Injective (state s).ancestor) :
    currentNoFirstMerger N s t =ᵐ[currentPairClockMeasure N r s] observedSurvival N s t := by
  have hm : currentPairClockMeasure N r s (observedSurvival N s t) =
      currentPairClockMeasure N r s (currentNoFirstMerger N s t) := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [actual_observed_survival_mass, actual_discrete_survival N r t s hs,
      actual_current_clock_no_merger]
  exact ae_eq_of_subset_of_measure_ge (no_first_subset_observed N s t hs) hm.le
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)).nullMeasurableSet
    (measure_ne_top _ _)

/-- The genuine ancestry-observed event gives the actual source future on
its original clock vector, with its measured positive denominator. -/
theorem actual_observed_conditioned_future (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (t u : ℝ≥0)
    (hs : Function.Injective (state s).ancestor) :
    (ENNReal.ofReal ((currentPairClockMeasure N r s) (observedSurvival N s t)).toReal)⁻¹ •
      (((currentPairClockMeasure N r s).restrict (observedSurvival N s t)).map
        (literalClockEndpoint N (Fintype.card Copy) ((t : ℝ) + (u : ℝ)) s)) =
      (sourceTimeKernel N r u s).toMeasure.map some := by
  have h := actual_observed_survival_ae N r s t hs
  rw [← measure_congr h, ← Measure.restrict_congr_set h]
  exact original_conditioned_future_source_law N r s t u

/-- A long actual record can be read at a cut, without adding a boundary or
regenerating a stochastic path. This is a deterministic same-record identity. -/
theorem observed_survival_from_long_record (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t h : ℝ≥0) (ht : t ≤ h) :
    {c | discreteReadout N (cutEndpoint N (Fintype.card Copy) (t : ℝ) s
      (literalMarkedTrace N (Fintype.card Copy) (h : ℝ) s c).2) = true} =
      observedSurvival N s t := by
  ext c
  simp only [Set.mem_setOf_eq]
  rw [actual_history_cut_readout N (Fintype.card Copy) t h s c (by exact_mod_cast ht)]
  rfl

#print axioms actual_epoch_endpoint_law
#print axioms actual_observed_survival_ae
#print axioms actual_observed_conditioned_future
#print axioms observed_survival_from_long_record
end GProgram.G5.ObservedEpochConditioning
