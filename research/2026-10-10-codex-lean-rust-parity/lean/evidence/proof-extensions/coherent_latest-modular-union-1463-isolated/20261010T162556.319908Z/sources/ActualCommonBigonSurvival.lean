import ActualBigonBinomial

/-! Conditional COMMON primitive: the actual original register is retained.
Contributor: dot (OpenAI), 9 October 2026. No fresh-register independence. -/
namespace DotG34.ActualCommonBigonSurvival
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceActualHoldingClocks
open DotG34.ActualBigonRate DotG34.ActualBigonSurvival DotG34.ActualPulseSurvival
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_common_bigon_survival (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (H : GProgram.G2.OriginalHybridParents N)
    (t : ℝ≥0) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid) :
    let n := Fintype.card (AtNode (state s) H.hybrid)
    (((sourceProgram N r [.boundary (.common H), .interval t] s).map liveCard)
      (liveCard s)).toReal =
    if (state s).register H.hybrid then
      (Real.exp (-(pairRate r (some H.parent1)*(t:ℝ))))^(n.choose 2)
    else (Real.exp (-(pairRate r (some H.parent0)*(t:ℝ))))^(n.choose 2) := by
  dsimp only
  rw [actual_common_epoch_survival, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    actual_bigon_holding N r H s hall]
  cases hreg : (state s).register H.hybrid <;> simp [hreg,coinCount]

#print axioms actual_common_bigon_survival
end DotG34.ActualCommonBigonSurvival
