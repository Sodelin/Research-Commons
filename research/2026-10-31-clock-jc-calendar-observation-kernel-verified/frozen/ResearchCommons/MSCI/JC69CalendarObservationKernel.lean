import ResearchCommons.MSCI.JC69WeightedCalendar
import ResearchCommons.MSCI.JC69FixedBankBoundary

/-! Actual raw endpoint fibres to the accepted weighted observation kernel.
UNCOMPILED candidate, dot (OpenAI), 31 October 2026. No small-state bound,
normalization of killed weights, or root ancestry assumption is hidden here. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69CalendarObservationKernel
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open GProgram.G2.ActualCalendarTrace GProgram.G2.LiteralMarkedClockTrace
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69TraceOccupation
open ResearchCommons.MSCI.JC69EndpointWeight ResearchCommons.MSCI.JC69EndpointQuotient
open ResearchCommons.MSCI.JC69WeightedCalendar ResearchCommons.MSCI.JC69FixedBankBoundary
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Aggregate the original raw-code fibres, retaining the SAME endpoint
observation. This finite ambient observation type is not claimed to have S elements. -/
def segmentObservedWeight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (op : ProgramStep N) (s : Code N sample)
    (target : BlockPopulationObservation Copy V E) : ℝ≥0∞ :=
  ∑ d : Code N sample, segmentFibreWeight N r L q op s d *
    (if observeCode N d = target then 1 else 0)

lemma actual_fibre_readout (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (op : ProgramStep N) (s : Code N sample) (F : Code N sample → ℝ≥0∞) :
    (∑ d : Code N sample, segmentFibreWeight N r L q op s d * F d) =
      ∫⁻ z, segmentWeight N L q op s z * F z.2 ∂actualSegmentLaw N r op s := by
  rw [← finite_fibre_lintegral (actualSegmentLaw N r op s) Prod.snd measurable_snd
    (fun z => segmentWeight N L q op s z * F z.2)]
  apply Finset.sum_congr rfl
  intro d _
  rw [segmentFibreWeight,← lintegral_mul_const (F d) (segment_weight_measurable N L q op s)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem
    (measurableSet_eq_fun measurable_snd measurable_const :
      MeasurableSet {z : SegmentRecord N sample | z.2 = d})] with z hz
  rw [hz]

/-- Exact original interval supplier, at the original full-copy fuel and
nonnegative physical duration. No new readout or source law is substituted. -/
theorem actual_interval_observation_weight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (s : Code N sample) (h : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    segmentObservedWeight N r L q (.interval h) s target =
      actualResolvedWeight N r L q (Fintype.card Copy) s h target := by
  rw [segmentObservedWeight,actual_fibre_readout]
  have hm : Measurable (fun z : SegmentRecord N sample =>
      segmentWeight N L q (.interval h) s z *
        (if observeCode N z.2 = target then (1:ℝ≥0∞) else 0)) :=
    (segment_weight_measurable N L q (.interval h) s).mul
      ((measurable_of_countable (fun d : Code N sample =>
        if observeCode N d = target then (1:ℝ≥0∞) else 0)).comp measurable_snd)
  rw [actualSegmentLaw,lintegral_map hm (attach_endpoint_measurable N s)]
  rfl

/-- Boundary coefficient is the actual current-block routing PMF pushed to
observations, with the original bank still held fixed. -/
theorem actual_boundary_observation_weight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (b : BoundaryOperation N) (s : Code N sample)
    (target : BlockPopulationObservation Copy V E) :
    segmentObservedWeight N r L q (.boundary b) s target =
      ((boundaryKernel N b s).map (observeCode N)) target := by
  simp only [segmentObservedWeight,actual_boundary_fibre_weight,PMF.map_apply,tsum_fintype]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : observeCode N d = target
  · simp [h]
  · simp [h,Ne.symm h]

/-- SAME observation and SAME original register suffice for the actual
one-step weighted kernel; interval register independence is inherited. -/
theorem actual_segment_observation_quotient (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (op : ProgramStep N) (s t : Code N sample)
    (hobs : observeCode N s = observeCode N t)
    (hreg : (state s).register = (state t).register)
    (target : BlockPopulationObservation Copy V E) :
    segmentObservedWeight N r L q op s target = segmentObservedWeight N r L q op t target := by
  cases op with
  | interval h =>
      rw [actual_interval_observation_weight,actual_interval_observation_weight]
      exact actual_resolved_weight_quotient N r L q (Fintype.card Copy) s t h target hobs
  | boundary b =>
      rw [actual_boundary_observation_weight,actual_boundary_observation_weight]
      exact congrArg (fun p : PMF (BlockPopulationObservation Copy V E) => p target)
        (actual_fixed_bank_boundary_quotient N b s t hobs hreg)

/-- A genuinely observation-factored future readout can be transported;
this does not assume that the whole calendar future already factors. -/
theorem actual_observation_readout_sum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (op : ProgramStep N) (s : Code N sample)
    (F : BlockPopulationObservation Copy V E → ℝ≥0∞) :
    (∑ d : Code N sample, segmentFibreWeight N r L q op s d * F (observeCode N d)) =
      ∑ target : BlockPopulationObservation Copy V E,
        segmentObservedWeight N r L q op s target * F target := by
  simp_rw [segmentObservedWeight,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp

/-- Zero source endpoint mass gives zero weighted fibre without asserting
that a killed transition is normalized, or requiring a new mass bound. -/
theorem actual_fibre_zero_of_source_zero (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (op : ProgramStep N) (s d : Code N sample)
    (hz : sourceProgramStep N r op s d = 0) :
    segmentFibreWeight N r L q op s d = 0 := by
  have he : actualSegmentLaw N r op s {z | z.2 = d} = 0 :=
    (segment_end_fibre_mass N r op s d).trans hz
  have hm : MeasurableSet {z : SegmentRecord N sample | z.2 = d} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have hr : (actualSegmentLaw N r op s).restrict {z | z.2 = d} = 0 :=
    Measure.restrict_eq_zero.mpr he
  simp [segmentFibreWeight,hr]

#print axioms actual_interval_observation_weight
#print axioms actual_boundary_observation_weight
#print axioms actual_segment_observation_quotient
#print axioms actual_observation_readout_sum
#print axioms actual_fibre_zero_of_source_zero
end ResearchCommons.MSCI.JC69CalendarObservationKernel
