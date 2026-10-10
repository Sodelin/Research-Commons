import G2CutResidualSourceMixture
import G2CompleteAncestralPath
import G2SourceFiniteHistory

/-!
Actual ordered finite histories on one original clock vector, identified with
the original finite source-kernel history PMF. Contributor: dot (OpenAI),
6 October 2026. The history observable is defined directly from the literal
clock compiler; the Markov recursion is proved from retained-clock attachment.
-/
namespace GProgram.G2.ActualEpochHistoryLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourcePoissonKernel
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.LiteralCutResidual
open GProgram.G2.SameClockContinuation GProgram.G2.SameClockPastFutureLaw
open GProgram.G2.HistoryResidualAttachment GProgram.G2.CutResidualSourceMixture
open GProgram.G2.CompleteAncestralPath GProgram.G2.SourceFiniteHistory
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

noncomputable def cumulativeTimes : (ds : List ℝ≥0) → Fin ds.length → ℝ≥0
  | [] => fun i => Fin.elim0 i
  | t::ds => Fin.cons t (fun i => t+cumulativeTimes ds i)

noncomputable def actualEpochHistory (N : RootedBinary V E X) {sample : Copy → X}
    (ds : List ℝ≥0) (s : Code N sample) (c : Choice N s → ℝ) : Fin ds.length → Code N sample :=
  fun i => literalEpochPath N s c (cumulativeTimes ds i)

lemma actual_epoch_history_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ds : List ℝ≥0) (s : Code N sample) : Measurable (actualEpochHistory N ds s) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply (cumulativeTimes ds i)).comp (literal_epoch_path_measurable N s)

def consHistory (N : RootedBinary V E X) {sample : Copy → X} (n : Nat)
    (d : Code N sample) (z : Fin n → Code N sample) : Fin (n+1) → Code N sample := Fin.cons d z

lemma cons_history_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (d : Code N sample) : Measurable (consHistory N n d) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · exact measurable_pi_apply j

noncomputable def residualHistory (N : RootedBinary V E X) {sample : Copy → X}
    (ds : List ℝ≥0) (s : Code N sample) : CutResidual N sample → Fin (ds.length+1) → Code N sample
  | .inl _ => fun _ => s
  | .inr z => consHistory N ds.length z.1 (actualEpochHistory N ds z.1 z.2)

lemma residual_history_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ds : List ℝ≥0) (s : Code N sample) : Measurable (residualHistory N ds s) := by
  have hm : Measurable (fun z : (Σ d : Code N sample, Choice N d → ℝ) =>
      consHistory N ds.length z.1 (actualEpochHistory N ds z.1 z.2)) := by
    intro A hA
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro d
    exact ((cons_history_measurable N ds.length d).comp
      (actual_epoch_history_measurable N ds d)) hA
  exact measurable_const.sumElim hm

lemma literal_endpoint_total_on_regular (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (hc : ClockRegular c) (hn : liveCard s ≤ n) :
    literalClockEndpoint N n t s c =
      some (traceEndpoint N n s (literalMarkedTrace N n t s c).2) := by
  rw [← marked_trace_endpoint_eq N n s t c]
  simp only [decodedEndpoint,marked_trace_success_on_regular N n s t c hn hc,if_true]

/-- Every later coordinate continues on the retained original clocks. The
failure value of residualHistory is excluded by the proved success event. -/
theorem actual_history_continuation (N : RootedBinary V E X) {sample : Copy → X}
    (t : ℝ≥0) (ds : List ℝ≥0) (s : Code N sample) (c : Choice N s → ℝ)
    (hc : ClockRegular c) :
    actualEpochHistory N (t::ds) s c =
      residualHistory N ds s (literalCutResidual N (Fintype.card Copy) t s c) := by
  have hn : liveCard s ≤ Fintype.card Copy := Finset.card_le_univ s.val.live
  obtain ⟨d,k,hcut⟩ := actual_cut_residual_success N (Fintype.card Copy) t s c hc hn
  have hk := residual_regular_and_card N (Fintype.card Copy) t s d c k hc hcut
  have hdn : liveCard d ≤ Fintype.card Copy := le_trans hk.1 hn
  rw [hcut]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have he : literalClockEndpoint N (Fintype.card Copy) t s c = some d := by
      rw [← cut_endpoint_eq_literal N (Fintype.card Copy) s t c,hcut]
      rfl
    rw [literal_endpoint_total_on_regular N _ t s c hc hn] at he
    exact Option.some.inj he
  · have he := same_clock_endpoint_continuation N (Fintype.card Copy) t
      (cumulativeTimes ds j) s d c k hc hn t.coe_nonneg (cumulativeTimes ds j).coe_nonneg hcut
    rw [literal_endpoint_total_on_regular N _ _ s c hc hn,
      literal_endpoint_total_on_regular N _ _ d k hk.2 hdn] at he
    exact Option.some.inj he

/-- Actual finite-vector renewal; the coefficients and residual products are
those of the original source law, derived rather than postulated. -/
theorem actual_epoch_history_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (ds : List ℝ≥0) (s : Code N sample) :
    (currentPairClockMeasure N r s).map (actualEpochHistory N (t::ds) s) =
      ∑ d : Code N sample, sourceTimeKernel N r t s d •
        (((currentPairClockMeasure N r d).map (actualEpochHistory N ds d)).map
          (consHistory N ds.length d)) := by
  have he : actualEpochHistory N (t::ds) s =ᵐ[currentPairClockMeasure N r s]
      (fun c => residualHistory N ds s (literalCutResidual N (Fintype.card Copy) t s c)) := by
    filter_upwards [actual_current_clock_regular_ae N r s] with c hc
    exact actual_history_continuation N t ds s c hc
  rw [Measure.map_congr he,actual_cut_readout_source_law N r s t
    (residualHistory N ds s) (residual_history_measurable N ds s)]
  apply Finset.sum_congr rfl
  intro d _
  rw [Measure.map_map (cons_history_measurable N ds.length d)
    (actual_epoch_history_measurable N ds d)]
  rfl

noncomputable def epochSourceHistoryLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ds : List ℝ≥0) (s : Code N sample) :
    PMF (Fin ds.length → Code N sample) :=
  historyLaw (fun (t : ℝ≥0) (d : Code N sample) => sourceTimeKernel N r t d) ds s

/-- Full actual ordered-history identification, including zero increments and
empty histories/carriers. The original clock observable was defined directly. -/
theorem actual_epoch_history_source_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ds : List ℝ≥0) (s : Code N sample) :
    (currentPairClockMeasure N r s).map (actualEpochHistory N ds s) =
      (epochSourceHistoryLaw N r ds s).toMeasure := by
  induction ds generalizing s with
  | nil =>
      letI := GProgram.G2.HistoryResidualAttachment.current_clock_probability N r s
      have hp : actualEpochHistory N [] s = (fun _ => (fun i : Fin 0 => Fin.elim0 i)) := by
        funext c i
        exact Fin.elim0 i
      rw [hp,Measure.map_const]
      simp [epochSourceHistoryLaw,historyLaw,PMF.toMeasure_pure]
  | cons t ds ih =>
      rw [actual_epoch_history_renewal]
      simp_rw [ih,PMF.toMeasure_map _ _ (cons_history_measurable N ds.length _)]
      apply Measure.ext
      intro A hA
      rw [Measure.finsetSum_apply,epochSourceHistoryLaw,historyLaw,
        PMF.toMeasure_bind_apply _ _ A hA,tsum_fintype]
      simp only [Measure.smul_apply,smul_eq_mul,consHistory,epochSourceHistoryLaw]
      rfl

#print axioms actual_epoch_history_measurable
#print axioms cons_history_measurable
#print axioms residual_history_measurable
#print axioms literal_endpoint_total_on_regular
#print axioms actual_history_continuation
#print axioms actual_epoch_history_renewal
#print axioms actual_epoch_history_source_law
end GProgram.G2.ActualEpochHistoryLaw
