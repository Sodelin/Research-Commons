import G7OriginalSurvivalCoverage

/-!
G6 consumer of the existing original G7 whole-edge physical chart.

Contributor: Codex / lean_reuse_successor, 2026-10-10. Proposal; uncompiled.
The preserved predecessor is G6OriginalWholeEdgeSurvivalLift, SHA256
9aff47125e6a7d9ec1d6c7cc4550368f918e1b2ee8efce684c49232d8a690850.
This file reuses G7's realization and completed-law proof rather than defining
another logarithmic bank. The graph, strict calendar, registry and positive
exposures are supplied. It constructs no compressed source, protected-bin
transport, timed observer, rational rate encoding or effective policy.
-/
namespace GProgram.G6.OriginalWholeEdgeChartConsumer

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open GProgram.G7.OriginalSurvivalCoverage

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Rate assignment on a supplied graph/calendar with positive desired
whole-edge exposures. Source admission and the positive exposures themselves
must already have been established by the reconstruction consumer. -/
theorem supplied_positive_exposure_image (N : RootedBinary V E X)
    (C : Calendar N.graph) (ell : E → ℝ) (hell : ∀ e, 0 < ell e) :
    ∃ r : PositivePairRates E,
      pairRate r none = 1 ∧ ∀ e, exposure N C r e = ell e := by
  exact ⟨ratesFromLengths N C ell hell, rfl,
    ratesFromLengths_exposure N C ell hell⟩

/-- One bank realizes every supplied interior whole-edge/coin coordinate and
represents the natural and ALL original controlled completed laws. The same
rate/inheritance bank is chosen before the comparison calendar and control row.
The inheritance coordinate is the ORIGINAL gamma, P(parent1). -/
theorem whole_edge_original_coin_chart (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (z : E → ℝ) (g : Hybrid N → ℝ)
    (hz : OpenCube z) (hg : ∀ h, 0 < g h ∧ g h < 1) :
    ∃ r : PositivePairRates E, ∃ p : HybridProbabilities N,
      pairRate r none = 1 ∧ survival N C r = z ∧ p.gamma = g ∧
      ∀ (D : Calendar N.graph) (s : PositivePairRates E), survival N D s = z →
        naturalCompletedLaw N D sample H p common s =
          naturalCompletedLaw N C sample H p common r ∧
        ∀ mask : OriginalMask N,
          controlledCompletedLaw N D sample H p common s mask =
            controlledCompletedLaw N C sample H p common r mask := by
  let p : HybridProbabilities N := ⟨g, fun h => (hg h).1, fun h => (hg h).2⟩
  let r := ratesFromSurvival N C z hz
  have hchart := actual_source_survival_chart N C sample H p common z hz
  change survival N C r = z ∧ _ at hchart
  exact ⟨r, p, rfl, hchart.1, rfl, hchart.2⟩

#print axioms supplied_positive_exposure_image
#print axioms whole_edge_original_coin_chart

end GProgram.G6.OriginalWholeEdgeChartConsumer
