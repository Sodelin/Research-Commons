import AstraSelectedCopy

/-! Source-only interface audit; neither native refinement nor physical admission.
The configuration type intentionally has no Fintype assumption. -/
set_option autoImplicit false

namespace Astra.IntegrationInterfaceAudit.SelectedCopies

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open GProgram.G2.LiteralTimedObservationPruning
open Astra.SelectedCopyReadout
open scoped Classical

universe uV uE uX uCopy uConfig
variable {V : Type uV} {E : Type uE} {X : Type uX}
variable {Copy : Type uCopy} {Config : Type uConfig}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

-- The selected carrier is an original-copy subtype, not a graph vertex ID.
example (sample : Copy → X) (keep : Finset Copy) (x : SelectedCopy keep) :
    selectedSample sample keep x = sample x.val := rfl

example (N : RootedBinary V E X) :
    OriginalMask N = (Hybrid N → Option Bool) := rfl

example (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (keep : Finset Copy) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (mask : OriginalMask N) :
    ((controlledCompletedUnrankedLaw N C sample H p common r mask).map
      (pruneForest keep)) =
    (controlledCompletedUnrankedLaw N C (selectedSample sample keep) H p common r mask).map
      (fun F => F.image (mapUnranked Subtype.val)) :=
  controlled_pruned_full_eq_selected N C sample keep H p common r mask

-- One complete configuration draw stays OUTSIDE source evolution and pruning;
-- there is no replacement by products of site marginals or per-copy masks.
example (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (keep : Finset Copy) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (ν : PMF Config) (masks : Config → OriginalMask N) :
    ((ν.bind (fun cfg =>
      controlledCompletedUnrankedLaw N C sample H p common r (masks cfg))).map
        (pruneForest keep)) =
    ν.bind (fun cfg =>
      (controlledCompletedUnrankedLaw N C (selectedSample sample keep)
        H p common r (masks cfg)).map
          (fun F => F.image (mapUnranked Subtype.val))) :=
  randomized_pruned_full_eq_selected N C sample keep H p common r ν masks

end Astra.IntegrationInterfaceAudit.SelectedCopies

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.notation false
set_option pp.proofs false

#print UnifiedLean.Source.SourceCopyCarrierTransport.SelectedCopy
#print UnifiedLean.Source.SourceCopyCarrierTransport.selectedSample
#print UnifiedLean.Source.OriginalFixedIDControls.OriginalMask
#print GProgram.G2.LiteralTimedObservationPruning.pruneForest
#print UnifiedLean.Source.ControlledUnrankedSourceProjectivity.controlledCompletedUnrankedLaw
#check @Astra.SelectedCopyReadout.controlled_pruned_full_eq_selected
#check @Astra.SelectedCopyReadout.randomized_pruned_full_eq_selected
#check @GProgram.G2.LiteralTimedObservationPruning.prune_source_forest
#check @UnifiedLean.Source.ControlledUnrankedSourceProjectivity.actual_controlled_complete_unranked_all_panel_projectivity
#print axioms Astra.SelectedCopyReadout.controlled_pruned_full_eq_selected
#print axioms Astra.SelectedCopyReadout.randomized_pruned_full_eq_selected
#print axioms GProgram.G2.LiteralTimedObservationPruning.prune_source_forest
#print axioms UnifiedLean.Source.ControlledUnrankedSourceProjectivity.actual_controlled_complete_unranked_all_panel_projectivity
