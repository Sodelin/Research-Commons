import G2HistoryResidualAttachment

/-!
Source-PMF future generated from the actual retained cut clocks.
Contributor: dot (OpenAI), 6 October2026. Development source.
This does not identify the generated future with the original compiler at
t+v; that requires the separate deterministic continuation theorem.
-/
namespace GProgram.G2.CutFutureSourceBinding
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourcePoissonKernel
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.LiteralEpochLaw
open GProgram.G2.LiteralCutResidual GProgram.G2.HistoryResidualAttachment
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.HistoryResidualAttachment.current_clock_probability

noncomputable def retainedFutureEndpoint (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (v : ℝ) : CutResidual N sample → Option (Code N sample) :=
  Sum.elim (fun _ => none) (fun z => literalClockEndpoint N n v z.1 z.2)

lemma retained_future_endpoint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (v : ℝ) : Measurable (retainedFutureEndpoint N (sample := sample) n v) := by
  have hm : Measurable (fun z : (Σ d : Code N sample, Choice N d → ℝ) =>
      literalClockEndpoint N n v z.1 z.2) := by
    intro A hA
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro d
    exact (literal_endpoint_measurable N n d v) hA
  exact measurable_const.sumElim hm

@[simp] lemma retained_future_encode (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (v : ℝ) (d : Code N sample) (c : Choice N d → ℝ) :
    retainedFutureEndpoint N n v (encodeResidual N d c) = literalClockEndpoint N n v d c := rfl

/-- Derived source-PMF future from the same retained residual vector, jointly
with the entire recorded epoch history. Every history fibre stays unnormalized. -/
theorem actual_retained_future_source_binding (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t v : ℝ≥0)
    (hn : liveCard s ≤ n) :
    (actualCutJointLaw N r n s (t : ℝ)).map
      (Prod.map id (retainedFutureEndpoint N (Fintype.card Copy) (v : ℝ))) =
      ∑ d : Code N sample,
        ((actualMarkedTraceLaw N r n s (t : ℝ)).restrict {h | decodedEndpoint N n s h = some d}).prod
          ((sourceTimeKernel N r v d).toMeasure.map some) := by
  letI := actual_marked_trace_probability N r n s t
  have hm : Measurable (Prod.map (id : Bool × ClockTrace N sample n → Bool × ClockTrace N sample n)
      (retainedFutureEndpoint N (Fintype.card Copy) (v : ℝ))) :=
    measurable_id.prodMap (retained_future_endpoint_measurable N (sample := sample)
      (Fintype.card Copy) (v : ℝ))
  rw [actual_full_past_terminal_fibres N r n s t hn,Measure.map_finset_sum' hm.aemeasurable]
  apply Finset.sum_congr rfl
  intro d _
  have he : Measurable (fun z : (Bool × ClockTrace N sample n) × (Choice N d → ℝ) =>
      (z.1,encodeResidual N d z.2)) :=
    measurable_fst.prodMk ((encode_residual_measurable N d).comp measurable_snd)
  rw [Measure.map_map hm he]
  change ((((actualMarkedTraceLaw N r n s (t : ℝ)).restrict
      {h | decodedEndpoint N n s h = some d}).prod (currentPairClockMeasure N r d)).map
        (Prod.map id (literalClockEndpoint N (Fintype.card Copy) (v : ℝ) d))) = _
  rw [← Measure.map_prod_map _ _ measurable_id (literal_endpoint_measurable N _ d v),
    Measure.map_id,original_copy_cap_literal_epoch_law N r d v]

/-- The same identity written directly as a pushforward of the original
clock vector. The future is read from its literal retained cut residuals. -/
theorem original_clock_past_retained_future_binding (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t v : ℝ≥0)
    (hn : liveCard s ≤ n) :
    (currentPairClockMeasure N r s).map (fun c =>
      (literalMarkedTrace N n (t : ℝ) s c,
        retainedFutureEndpoint N (Fintype.card Copy) (v : ℝ) (literalCutResidual N n (t : ℝ) s c))) =
      ∑ d : Code N sample,
        ((actualMarkedTraceLaw N r n s (t : ℝ)).restrict {h | decodedEndpoint N n s h = some d}).prod
          ((sourceTimeKernel N r v d).toMeasure.map some) := by
  have hm : Measurable (Prod.map (id : Bool × ClockTrace N sample n → Bool × ClockTrace N sample n)
      (retainedFutureEndpoint N (Fintype.card Copy) (v : ℝ))) :=
    measurable_id.prodMap (retained_future_endpoint_measurable N (sample := sample)
      (Fintype.card Copy) (v : ℝ))
  calc
    _ = (actualCutJointLaw N r n s (t : ℝ)).map
        (Prod.map id (retainedFutureEndpoint N (Fintype.card Copy) (v : ℝ))) := by
      rw [actualCutJointLaw,Measure.map_map hm
        ((marked_trace_measurable N n s t).prodMk (literal_cut_measurable N n s t))]
      rfl
    _ = _ := actual_retained_future_source_binding N r n s t v hn

#print axioms retained_future_endpoint_measurable
#print axioms retained_future_encode
#print axioms actual_retained_future_source_binding
#print axioms original_clock_past_retained_future_binding
end GProgram.G2.CutFutureSourceBinding
