import G6OriginalWholeEdgeChartConsumer

/-!
# One original physical bank before choosing mode or response row

G3 continuation, 21 October 2026. Source candidate, NOT COMPILED here.
Reuses the whole-edge chart; it constructs no new graph, protected word,
polynomial compiler, witness bound, complete NO language or G3 endpoint.

The chosen rates and natural inheritance bank are independent of `common`
and `sample`. This makes the quantifier order needed by a joint BOTH input
explicit, rather than choosing a different existential bank in each mode.
Original gamma is P(parent1), as in the inherited chart.

Pinned dependencies and limits are recorded in G3-LEAN-SHARED-BANK-NOTE.md.
-/
namespace GProgram.G3.WholeEdgeSharedBank

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

/-- A supplied graph, strict calendar, original registry and interior survival/
coin tuple determine one physical bank before ANY mode, sampling allocation,
comparison calendar or original mask is selected. No algebraic rate encoding
is asserted: logarithms realize the algebraic survival-coordinate witness. -/
theorem whole_edge_original_coin_chart_all_modes
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (z : E → ℝ) (g : Hybrid N → ℝ)
    (hz : OpenCube z) (hg : ∀ h, 0 < g h ∧ g h < 1) :
    ∃ r : PositivePairRates E, ∃ p : HybridProbabilities N,
      pairRate r none = 1 ∧ survival N C r = z ∧ p.gamma = g ∧
      ∀ (common : Hybrid N → Bool) (sample : Copy → X)
        (D : Calendar N.graph) (s : PositivePairRates E),
        survival N D s = z →
          naturalCompletedLaw N D sample H p common s =
            naturalCompletedLaw N C sample H p common r ∧
          ∀ mask : OriginalMask N,
            controlledCompletedLaw N D sample H p common s mask =
              controlledCompletedLaw N C sample H p common r mask := by
  let p : HybridProbabilities N := ⟨g, fun h => (hg h).1, fun h => (hg h).2⟩
  let r := ratesFromSurvival N C z hz
  refine ⟨r, p, rfl, ratesFromSurvival_survival N C z hz, rfl, ?_⟩
  intro common sample D s hs
  have hchart := actual_source_survival_chart N C sample H p common z hz
  change survival N C r = z ∧ _ at hchart
  exact hchart.2 D s hs

#print axioms whole_edge_original_coin_chart_all_modes

end GProgram.G3.WholeEdgeSharedBank
