import ActualSerialSurvival

/-! Actual current-owner pulse followed by an ordinary epoch.
Contributor: dot (OpenAI), 9 October 2026. Source specialization of the accepted
whole-prefix mass expansion. The register is unchanged; no scalar arm law is assumed. -/
namespace DotG34.ActualPulseSurvival
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G5.ActualNoMergerReadout GProgram.G5.ActualRoutingSupport
open DotG34.ActualSerialSurvival
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The law sums over exactly the current owners at this actual original hybrid.
The finite coins have the current source convention, true=parent1. -/
theorem actual_independent_epoch_survival
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (H : GProgram.G2.OriginalHybridParents N)
    (gamma : unitInterval) (t : ℝ≥0) (s : Code N sample) :
    ((sourceProgram N r [.boundary (.independent H gamma), .interval t] s).map
      liveCard) (liveCard s) =
    ∑ coin : AtNode (state s) H.hybrid → Bool,
      currentCoinPMF (AtNode (state s) H.hybrid) gamma coin *
        ENNReal.ofReal (Real.exp (-(totalRate N r (pulseCode H s coin)*(t:ℝ)))) := by
  simp only [sourceProgram, sourceProgramStep, PMF.bind_pure,
    boundaryKernel, independentPulseKernel, PMF.bind_map, PMF.map_bind]
  rw [PMF.bind_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro coin _
  have hc : liveCard (pulseCode H s coin) = liveCard s := rfl
  rw [← hc, actual_kernel_live_card_mass, actual_holding_weight]

/-- COMMON uses the already sampled original register, with no fresh coin. -/
theorem actual_common_epoch_survival
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (H : GProgram.G2.OriginalHybridParents N)
    (t : ℝ≥0) (s : Code N sample) :
    ((sourceProgram N r [.boundary (.common H), .interval t] s).map liveCard)
      (liveCard s) =
    ENNReal.ofReal (Real.exp (-(totalRate N r
      (pulseCode H s (fun _ => (state s).register H.hybrid))*(t:ℝ)))) := by
  simp only [sourceProgram, sourceProgramStep, PMF.bind_pure, boundaryKernel, PMF.pure_bind]
  have hc : liveCard (pulseCode H s (fun _ => (state s).register H.hybrid)) = liveCard s := rfl
  rw [← hc, actual_kernel_live_card_mass, actual_holding_weight]

#print axioms actual_independent_epoch_survival
#print axioms actual_common_epoch_survival
end DotG34.ActualPulseSurvival
