import G2CutFutureSourceBinding
import G2SameClockContinuation

/-!
The full recorded-past law and the actual later endpoint on the same original
clock vector. Contributor: dot (OpenAI), 6 October 2026.
The common copy-cardinality budget is explicit. Every endpoint fibre remains
an unnormalized measure; no pointwise conditional law on null histories is used.
-/
namespace GProgram.G2.SameClockPastFutureLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourcePoissonKernel
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.LiteralCutResidual
open GProgram.G2.HistoryResidualAttachment GProgram.G2.CutFutureSourceBinding
open GProgram.G2.SameClockContinuation
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

/-- Sufficient regular clocks cannot produce the residual failure marker. -/
theorem actual_cut_residual_success (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (hc : ClockRegular c) (hn : liveCard s ≤ n) :
    ∃ d k, literalCutResidual N n t s c = encodeResidual N d k := by
  have hs := marked_trace_success_on_regular N n s t c hn hc
  have he := cut_endpoint_eq_literal N n s t c
  have hm := marked_trace_endpoint_eq N n s t c
  cases hcut : literalCutResidual N n t s c with
  | inl u =>
      rw [hcut] at he
      have hnone : literalClockEndpoint N n t s c = none := he.symm
      rw [hnone] at hm
      simp [decodedEndpoint,hs] at hm
  | inr z =>
      obtain ⟨d,k⟩ := z
      exact ⟨d,k,rfl⟩

/-- The retained future reads the actual t+v endpoint, with no independent
resampling and no change of the original clock catalogue. -/
theorem retained_future_is_same_clock_endpoint (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t v : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (hc : ClockRegular c) (hn : liveCard s ≤ n) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    retainedFutureEndpoint N n v (literalCutResidual N n t s c) =
      literalClockEndpoint N n (t+v) s c := by
  obtain ⟨d,k,hcut⟩ := actual_cut_residual_success N n t s c hc hn
  rw [hcut,retained_future_encode]
  exact (same_clock_endpoint_continuation N n t v s d c k hc hn ht hv hcut).symm

/-- Exact joint source law of the whole recorded epoch history up to t and
the actual original-clock endpoint at t+v. This derives, rather than assumes,
the corresponding finite-history Markov factorization. -/
theorem actual_same_clock_past_future_source_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t v : ℝ≥0) :
    (currentPairClockMeasure N r s).map (fun c =>
      (literalMarkedTrace N (Fintype.card Copy) (t : ℝ) s c,
        literalClockEndpoint N (Fintype.card Copy) ((t : ℝ)+(v : ℝ)) s c)) =
      ∑ d : Code N sample,
        ((actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
          {h | decodedEndpoint N (Fintype.card Copy) s h = some d}).prod
          ((sourceTimeKernel N r v d).toMeasure.map some) := by
  have hn : liveCard s ≤ Fintype.card Copy := Finset.card_le_univ s.val.live
  have he : (fun c =>
      (literalMarkedTrace N (Fintype.card Copy) (t : ℝ) s c,
        literalClockEndpoint N (Fintype.card Copy) ((t : ℝ)+(v : ℝ)) s c)) =ᵐ[currentPairClockMeasure N r s]
      (fun c => (literalMarkedTrace N (Fintype.card Copy) (t : ℝ) s c,
        retainedFutureEndpoint N (Fintype.card Copy) (v : ℝ)
          (literalCutResidual N (Fintype.card Copy) (t : ℝ) s c))) := by
    filter_upwards [actual_current_clock_regular_ae N r s] with c hc
    congr 1
    exact (retained_future_is_same_clock_endpoint N (Fintype.card Copy)
      t v s c hc hn t.coe_nonneg v.coe_nonneg).symm
  rw [Measure.map_congr he]
  exact original_clock_past_retained_future_binding N r (Fintype.card Copy) s t v hn

#print axioms actual_cut_residual_success
#print axioms retained_future_is_same_clock_endpoint
#print axioms actual_same_clock_past_future_source_law
end GProgram.G2.SameClockPastFutureLaw
