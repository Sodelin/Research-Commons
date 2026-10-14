import G2LiteralTimedObservationPruning
import UnifiedLean.Source.ControlledUnrankedSourceProjectivity

/-!
Literal same-source pruning and the existing controlled selected-copy theorem,
composed pointwise under one complete configuration PMF. This is a source-law
composition, with no native implementation or physical admission premise added.
New source: compilation and axiom audit require their own execution receipts.
-/
namespace Astra.SelectedCopyReadout
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open GProgram.G2.LiteralTimedObservationPruning
open scoped Classical

variable {V E X Copy Config : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Retain the same N,C,H,p,r, mode assignment and original mask. -/
theorem controlled_pruned_full_eq_selected (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (mask : OriginalMask N) :
    ((controlledCompletedUnrankedLaw N C sample H p common r mask).map (pruneForest keep)) =
      (controlledCompletedUnrankedLaw N C (selectedSample sample keep) H p common r mask).map
        (fun F => F.image (mapUnranked Subtype.val)) := by
  rw [controlledCompletedUnrankedLaw, PMF.map_comp]
  have hp :
      (controlledCompletedLaw N C sample H p common r mask).map
        (fun d => pruneForest keep (sourceUnrankedForest (state d) Finset.univ)) =
      (controlledCompletedLaw N C sample H p common r mask).map
        (fun d => sourceUnrankedForest (state d) keep) := by
    congr 1
    funext d
    exact prune_source_forest (state d) d.property.forest keep
  change (controlledCompletedLaw N C sample H p common r mask).map
      (fun d => pruneForest keep (sourceUnrankedForest (state d) Finset.univ)) = _
  rw [hp]
  exact actual_controlled_complete_unranked_all_panel_projectivity N C sample keep H p common r mask

/-- A single joint configuration draw, with no marginal product or refitted bank. -/
theorem randomized_pruned_full_eq_selected (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (ν : PMF Config) (masks : Config → OriginalMask N) :
    ((ν.bind (fun cfg => controlledCompletedUnrankedLaw N C sample H p common r (masks cfg))).map
      (pruneForest keep)) =
    ν.bind (fun cfg =>
      (controlledCompletedUnrankedLaw N C (selectedSample sample keep) H p common r (masks cfg)).map
        (fun F => F.image (mapUnranked Subtype.val))) := by
  rw [PMF.map_bind]
  congr 1
  funext cfg
  exact controlled_pruned_full_eq_selected N C sample keep H p common r (masks cfg)

#print axioms controlled_pruned_full_eq_selected
#print axioms randomized_pruned_full_eq_selected
end Astra.SelectedCopyReadout
