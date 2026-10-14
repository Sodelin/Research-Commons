import G4ActualOriginalSpanDiagonal
import OriginalRegisterMarginal

/-!
# Once-drawn original-register averaging for actual private spans

Contributor: dot (OpenAI), 11 October 2026.
Additive source draft; compilation and independent review pending.

The conditional products are proved by G4ActualOriginalSpanDiagonal. Here
the actual natural original register is averaged once, with its original
site-dependent Bernoulli law. Mixed-mode words and shared register identities
are retained. The natural entrance below is the existing source-valid current
root entrance, not the law of an arbitrary conditioned interior cut.

For an arbitrary entrance-history law, reuse actual_entrance_mixture_no_loss;
replacing its weights by the natural weights requires the separate proved
no-read/source admission hypotheses. No such replacement is made here.
-/

namespace DotG34.ActualOriginalSpanNaturalAverage
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 MeasureTheory ProbabilityTheory
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceActualHoldingClocks
open G1ContextualForestReplacement G1OriginalDecoratedSpan
open DotG34.ActualOriginalSpanDiagonal
open scoped Classical BigOperators NNReal ENNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The same original hybrid parameter used by the natural bank and live-root
pulses. Nonhybrid values are inert. -/
noncomputable def vertexGamma (N : RootedBinary V E X) (p : HybridProbabilities N)
    (v : V) : unitInterval :=
  if hh : N.graph.IsHybrid v then originalGamma p ⟨v,hh⟩ else 0

noncomputable def naturalSpanLaw (N : RootedBinary V E X) (sample : Copy → X)
    (C : Calendar N.graph) (r : PositivePairRates E) (p : HybridProbabilities N)
    (common : V → Bool) {a b : V} (word : OriginalSpan N a b)
    (descendant : ∀ l, DescendsTo N (.node a) (sample l)) : PMF (Code N sample) :=
  (originalRegisterPMF N p).bind (fun register =>
    sourceProgram N r (spanProgram N C (vertexGamma N p) common word)
      (enteringCode N sample (.node a) register descendant))

private theorem entrance_no_loss (N : RootedBinary V E X) (sample : Copy → X)
    (C : Calendar N.graph) (r : PositivePairRates E) (gamma : V → unitInterval)
    (common : V → Bool) {a b : V} (word : OriginalSpan N a b)
    (descendant : ∀ l, DescendsTo N (.node a) (sample l)) (register : V → Bool) :
    ((sourceProgram N r (spanProgram N C gamma common word)
      (enteringCode N sample (.node a) register descendant)).map liveCard)
      (Fintype.card Copy) =
      spanDiagonal N C r gamma common register (Fintype.card Copy) word := by
  have hp : ∀ l ∈ (state (enteringCode N sample (.node a) register descendant)).live,
      (state (enteringCode N sample (.node a) register descendant)).location l = .node a := by
    intro l hl
    exact UnifiedLean.Source.FiniteSourceSnapshot.decode_encode_live_population
      N.root _ (enteringState_valid (.node a) register) (Finset.mem_univ l)
  have h := actual_original_span_no_loss N C r gamma common word
    (enteringCode N sample (.node a) register descendant) hp
  have hn : liveCard (enteringCode N sample (.node a) register descendant) =
      Fintype.card Copy := by
    change (Finset.univ : Finset Copy).card = Fintype.card Copy
    exact Finset.card_univ
  simpa only [hn, enteringCode_register] using h

/-- Exact natural averaging over the once-drawn ORIGINAL register. -/
theorem actual_natural_span_no_loss (N : RootedBinary V E X) (sample : Copy → X)
    (C : Calendar N.graph) (r : PositivePairRates E) (p : HybridProbabilities N)
    (common : V → Bool) {a b : V} (word : OriginalSpan N a b)
    (descendant : ∀ l, DescendsTo N (.node a) (sample l)) :
    ((naturalSpanLaw N sample C r p common word descendant).map liveCard)
      (Fintype.card Copy) =
      ∑' register, originalRegisterPMF N p register *
        spanDiagonal N C r (vertexGamma N p) common register (Fintype.card Copy) word := by
  rw [naturalSpanLaw, PMF.map_bind, PMF.bind_apply]
  apply tsum_congr
  intro register
  rw [entrance_no_loss]

/-- Equivalently expose the actual finite product-space coin assignment before
its fixed original-register map. This does not observe the latent assignment. -/
theorem actual_natural_span_coin_average (N : RootedBinary V E X) (sample : Copy → X)
    (C : Calendar N.graph) (r : PositivePairRates E) (p : HybridProbabilities N)
    (common : V → Bool) {a b : V} (word : OriginalSpan N a b)
    (descendant : ∀ l, DescendsTo N (.node a) (sample l)) :
    ((naturalSpanLaw N sample C r p common word descendant).map liveCard)
      (Fintype.card Copy) =
      ∑' coin, (originalRegisterMeasure N p).toPMF coin *
        spanDiagonal N C r (vertexGamma N p) common (originalRegister N coin)
          (Fintype.card Copy) word := by
  rw [naturalSpanLaw, originalRegisterPMF, PMF.bind_map, PMF.map_bind, PMF.bind_apply]
  apply tsum_congr
  intro coin
  simp only [Function.comp_apply]
  rw [entrance_no_loss]

theorem actual_original_coin_mass (N : RootedBinary V E X) (p : HybridProbabilities N)
    (coin : Hybrid N → Bool) :
    ((originalRegisterMeasure N p).toPMF coin).toReal =
      ∏ h : Hybrid N, if coin h then p.gamma h else 1-p.gamma h := by
  rw [Measure.toPMF_apply, originalRegisterMeasure, Measure.pi_singleton,
    ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro h hh
  cases hc : coin h <;>
    simp [bitMeasure, originalGamma, hc, ← measureReal_def, bernoulliMeasure_real_apply]

/-- A finite real formula with explicit original Bernoulli weights and the
derived chronological conditional products. No fresh per-cell register model. -/
theorem actual_natural_span_finite_real_average (N : RootedBinary V E X) (sample : Copy → X)
    (C : Calendar N.graph) (r : PositivePairRates E) (p : HybridProbabilities N)
    (common : V → Bool) {a b : V} (word : OriginalSpan N a b)
    (descendant : ∀ l, DescendsTo N (.node a) (sample l)) :
    (((naturalSpanLaw N sample C r p common word descendant).map liveCard)
      (Fintype.card Copy)).toReal =
      ∑ coin : Hybrid N → Bool, (∏ h : Hybrid N, if coin h then p.gamma h else 1-p.gamma h) *
        (spanDiagonal N C r (vertexGamma N p) common (originalRegister N coin)
          (Fintype.card Copy) word).toReal := by
  rw [actual_natural_span_coin_average, tsum_fintype,
    ENNReal.toReal_sum (fun coin _ => ENNReal.mul_ne_top
      (PMF.apply_ne_top _ _) (spanDiagonal_ne_top N C r _ _ _ _ word))]
  apply Finset.sum_congr rfl
  intro coin hc
  rw [ENNReal.toReal_mul, actual_original_coin_mass]

/-- In the calibrated equal-arm COMMON domain, the derived conditional
product is register-independent, so natural averaging leaves that product.
The hypothesis is a check on actual arm survivals, not the desired response. -/
theorem actual_natural_equal_common_arms_no_loss (N : RootedBinary V E X)
    (sample : Copy → X) (C : Calendar N.graph) (r : PositivePairRates E)
    (p : HybridProbabilities N) (common : V → Bool) {a b : V}
    (word : OriginalSpan N a b)
    (descendant : ∀ l, DescendsTo N (.node a) (sample l))
    (hequal : EqualCommonArms N C r common word) (register : V → Bool) :
    ((naturalSpanLaw N sample C r p common word descendant).map liveCard)
      (Fintype.card Copy) =
      spanDiagonal N C r (vertexGamma N p) common register (Fintype.card Copy) word := by
  rw [actual_natural_span_no_loss]
  simp_rw [spanDiagonal_register_independent N C r (vertexGamma N p) common
    _ register (Fintype.card Copy) word hequal]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end DotG34.ActualOriginalSpanNaturalAverage

#print axioms DotG34.ActualOriginalSpanNaturalAverage.actual_natural_span_no_loss
#print axioms DotG34.ActualOriginalSpanNaturalAverage.actual_natural_span_finite_real_average
#print axioms DotG34.ActualOriginalSpanNaturalAverage.actual_natural_equal_common_arms_no_loss
