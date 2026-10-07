import G2SameClockPastFutureLaw

/-!
# Actual source future conditioned on survival of an event-free epoch

Contributor: CLOUD-G5-20261007T155725Z, Codex, 2026-10-07.
Reuses dot's original-clock residual, same-clock continuation and literal
epoch-law providers unchanged. Compiler evidence is separately dated.

The endpoint is read from the ORIGINAL clock vector at t+u and conditioning
is the genuine no-first-merger event. Its sourceTimeKernel identity is derived
from the same-clock construction, not a desired conditional-law premise.
The encoded state retains current ancestors and their existing subtrees.

Scope: one actual event-free source epoch, initialized at a fixed admitted
state. The actual whole-calendar selected no-merger event, its finite state
posterior, original feasible-route positivity and five-partition row binding
remain separate G5-B/C1 obligations. This is not full master closure.
-/
namespace GProgram.G5.ActualNoEventEpoch
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourcePoissonKernel
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.LiteralEpochLaw
open GProgram.G2.LiteralCutResidual GProgram.G2.CutFutureSourceBinding
open GProgram.G2.SameClockPastFutureLaw
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

noncomputable def originalSurvivingFuture (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (t u : ℝ≥0) :
    Measure (Option (Code N sample)) :=
  ((currentPairClockMeasure N r s).restrict (currentNoFirstMerger N s t)).map
    (literalClockEndpoint N (Fintype.card Copy) ((t : ℝ) + (u : ℝ)) s)

/-- Unnormalized actual original-clock future. No route/observation equality
has been supplied as a source field. Later mergers use the actual current-root
catalogue and retain the complete old forest through sourceTimeKernel. -/
theorem original_surviving_future_source_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (t u : ℝ≥0) :
    originalSurvivingFuture N r s t u =
      ENNReal.ofReal (Real.exp (-(totalRate N r s * (t : ℝ)))) •
        ((sourceTimeKernel N r u s).toMeasure.map some) := by
  let μ := (currentPairClockMeasure N r s).restrict (currentNoFirstMerger N s t)
  let F := fun z : (Bool × ClockTrace N sample (Fintype.card Copy)) × CutResidual N sample =>
    retainedFutureEndpoint N (Fintype.card Copy) (u : ℝ) z.2
  have hF : Measurable F :=
    (retained_future_endpoint_measurable N (sample := sample) (Fintype.card Copy) (u : ℝ)).comp
      measurable_snd
  have hrecord : Measurable (fun c : Choice N s → ℝ =>
      (literalMarkedTrace N (Fintype.card Copy) (t : ℝ) s c,
       literalCutResidual N (Fintype.card Copy) (t : ℝ) s c)) :=
    (marked_trace_measurable N (Fintype.card Copy) s t).prodMk
      (literal_cut_measurable N (Fintype.card Copy) s t)
  have hencoded : Measurable (fun c : Choice N s → ℝ =>
      ((true, emptyTrace N (Fintype.card Copy) s), encodeResidual N s c)) :=
    measurable_const.prodMk (encode_residual_measurable N s)
  have heq := congrArg (fun ν => ν.map F)
    (actual_no_event_joint_residual N r (Fintype.card Copy) s t)
  rw [Measure.map_map hF hrecord, Measure.map_smul, Measure.map_map hF hencoded] at heq
  have hsame : (fun c : Choice N s → ℝ =>
      F (literalMarkedTrace N (Fintype.card Copy) (t : ℝ) s c,
         literalCutResidual N (Fintype.card Copy) (t : ℝ) s c)) =ᵐ[μ]
      literalClockEndpoint N (Fintype.card Copy) ((t : ℝ) + (u : ℝ)) s := by
    filter_upwards [ae_restrict_of_ae (actual_current_clock_regular_ae N r s)] with c hc
    exact retained_future_is_same_clock_endpoint N (Fintype.card Copy) t u s c hc
      (Finset.card_le_univ s.val.live) t.coe_nonneg u.coe_nonneg
  rw [Measure.map_congr hsame] at heq
  change originalSurvivingFuture N r s t u =
    ENNReal.ofReal (Real.exp (-(totalRate N r s * (t : ℝ)))) •
      (currentPairClockMeasure N r s).map
        (literalClockEndpoint N (Fintype.card Copy) (u : ℝ) s) at heq
  rw [original_copy_cap_literal_epoch_law N r s u] at heq
  exact heq

/-- Actual survival probability is strictly positive, even for empty current
pair catalogues. This is positivity, not a uniform demographic floor. -/
theorem actual_epoch_survival_positive (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) :
    0 < ((currentPairClockMeasure N r s) (currentNoFirstMerger N s t)).toReal := by
  rw [actual_current_clock_no_merger]
  exact Real.exp_pos _

/-- The denominator is the measured original survival event. It is not a
posterior supplied by the desired inverse theorem. -/
noncomputable def originalConditionedFuture (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (t u : ℝ≥0) :
    Measure (Option (Code N sample)) :=
  (ENNReal.ofReal (((currentPairClockMeasure N r s) (currentNoFirstMerger N s t)).toReal))⁻¹ •
    originalSurvivingFuture N r s t u

theorem original_conditioned_future_source_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (t u : ℝ≥0) :
    originalConditionedFuture N r s t u = (sourceTimeKernel N r u s).toMeasure.map some := by
  unfold originalConditionedFuture
  rw [actual_current_clock_no_merger, original_surviving_future_source_law, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
      ENNReal.ofReal_ne_top, one_smul]

#print axioms original_surviving_future_source_law
#print axioms actual_epoch_survival_positive
#print axioms original_conditioned_future_source_law
end GProgram.G5.ActualNoEventEpoch
