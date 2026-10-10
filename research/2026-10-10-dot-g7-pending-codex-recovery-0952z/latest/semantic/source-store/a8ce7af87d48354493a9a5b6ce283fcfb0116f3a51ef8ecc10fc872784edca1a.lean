import G7BoundaryRelabelling

/-! A fixed copy-index coin carrier for an actual CURRENT-owner pulse.
Contributor: dot, 2026-10-09. Unused bits are integrated out by the inherited
product-measure restriction theorem; no additional physical coin is observed.
This is an adapter for commuting distinct node operations within one boundary.
-/
namespace GProgram.G7.GlobalOwnerCoins
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest MeasureTheory
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceForestPulseMeasure
open scoped Classical
variable {V E Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [Fintype Copy] [DecidableEq Copy]

def restrictOwners (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (node : V) (c : Copy → Bool) : AtNode (state s) node → Bool :=
  fun l => c l.val

theorem restricted_pmf (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (node : V) (gamma : unitInterval) :
    (currentCoinPMF Copy gamma).map (restrictOwners N s node) =
      currentCoinPMF (AtNode (state s) node) gamma := by
  have h := coin_restriction_measurePreserving gamma
    (fun l : Copy => l ∈ (state s).live ∧ (state s).location l = .node node)
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (restrictOwners N s node) (currentCoinPMF Copy gamma) h.measurable]
  simp only [currentCoinPMF,Measure.toPMF_toMeasure]
  exact h.map_eq

/-- The actual source pulse kernel can be sampled on a fixed finite carrier;
only its actual current-owner restriction reaches the source destination. -/
theorem independent_pulse_fixed_carrier {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval) (s : Code N sample) :
    independentPulseKernel H gamma s =
      (currentCoinPMF Copy gamma).map (fun c => pulseCode H s (restrictOwners N s H.hybrid c)) := by
  rw [independentPulseKernel,← restricted_pmf N s H.hybrid gamma,PMF.map_comp]
  rfl

#print axioms restricted_pmf
#print axioms independent_pulse_fixed_carrier
end GProgram.G7.GlobalOwnerCoins
