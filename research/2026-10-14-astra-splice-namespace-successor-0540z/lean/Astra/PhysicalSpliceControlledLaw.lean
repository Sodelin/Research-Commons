import Astra.PhysicalSpliceWeights
import Astra.PhysicalSpliceConfiguration
import G4WholeProfileDetermination

/-!
# Controlled and whole-configuration COMMON laws of the constructed splice

Source-only composition, unselected and uncompiled. The pointwise weighted
identity is derived for the once-overridden original bank. Actual controlled
and randomized source-program forest PMFs then follow by the already proved
bank pushforwards. The whole configuration PMF and its identities are unchanged.
Pulling masks back along retainedHybrid is algebra; this module does not
authorize deletion of a protected or externally addressable controlled site.
-/

namespace Astra.PhysicalSpliceControlledLaw

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.OriginalFixedIDControls
open G1ActualTwoPortBlob G1SplicedSourceAdmission
open GProgram.G7.OriginalSurvivalCoverage
open DotG4.WeightedOrdinaryTreeLaw DotG4.WholeProfileDetermination
open Astra.PhysicalSpliceRates Astra.PhysicalSpliceRegistry
open Astra.PhysicalSpliceWeights Astra.OriginalBankRestriction
open Astra.PhysicalSpliceConfiguration
open G1CutChildPorts
open scoped Classical

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]

/-- Apply the proved weighted splice to the actual overridden whole bank.
No desired tree/law equality or restriction marginal is an input. -/
theorem weightedNormalize_override_splice (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E)
    (heq : exposure N C r A.fragment.parents.parent0 =
      exposure N C r A.fragment.parents.parent1)
    (mask : OriginalMask N) (coin : CommonSeed N) :
    weightedNormalize (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRegistry N hc b hb A H) (splicedRates N C r b A)
        (overrideBank (splicedNetwork N hc b hb A) (restrictMask N hc b hb A mask)
          (restrictBank N hc b hb A coin)) =
      weightedNormalize N C H r (overrideBank N mask coin) := by
  rw [← overrideBank_restrict N hc b hb A mask coin]
  exact weightedNormalize_splice N C H hc b hb A r heq (overrideBank N mask coin)

/-- The exact existing mask/tree interface inherits the pointwise identity. -/
theorem maskedNormalizedTree_splice (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E)
    (heq : exposure N C r A.fragment.parents.parent0 =
      exposure N C r A.fragment.parents.parent1)
    (mask : OriginalMask N) (coin : CommonSeed N) :
    maskedNormalizedTree (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRegistry N hc b hb A H) (splicedRates N C r b A)
        (restrictMask N hc b hb A mask) (restrictBank N hc b hb A coin) =
      maskedNormalizedTree N C H r mask coin := by
  exact weightedNormalize_override_splice N C H hc b hb A r heq mask coin

/-- Equality of the existing actual controlled source-program forest laws,
for every finite labelled copy allocation, from the actual original bank. -/
theorem controlledFullForestLaw_splice {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E)
    (heq : exposure N C r A.fragment.parents.parent0 =
      exposure N C r A.fragment.parents.parent1)
    (mask : OriginalMask N) (sample : Copy → X) :
    controlledFullForestLaw (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRegistry N hc b hb A H) (splicedProbabilities N hc b hb A p)
        (splicedRates N C r b A) (restrictMask N hc b hb A mask) sample =
      controlledFullForestLaw N C H p r mask sample := by
  rw [controlledFullForestLaw_tree_average, controlledFullForestLaw_tree_average,
    ← original_bank_restriction_pmf N hc b hb A p, PMF.bind_map]
  congr 1
  funext coin
  rw [maskedNormalizedTree_splice N C H hc b hb A r heq mask coin]

/-- Push forward the complete configuration/bank pair, preserving the exact
supplied configuration PMF, its dependence, and all zero-mass configurations. -/
theorem randomizedTreeLaw_splice {Config : Type*} [Fintype Config]
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E)
    (heq : exposure N C r A.fragment.parents.parent0 =
      exposure N C r A.fragment.parents.parent1)
    (ν : PMF Config) (masks : Config → OriginalMask N) :
    randomizedTreeLaw (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRegistry N hc b hb A H) (splicedProbabilities N hc b hb A p)
        (splicedRates N C r b A) ν (restrictMasks N hc b hb A masks) =
      randomizedTreeLaw N C H p r ν masks := by
  unfold randomizedTreeLaw
  rw [← configuration_bank_restriction_pmf N hc b hb A p ν, PMF.map_comp]
  congr 1
  funext z
  exact maskedNormalizedTree_splice N C H hc b hb A r heq (masks z.1) z.2

/-- The same constructed source tuple works before arbitrary configurations,
copy allocations and forest events. This is a COMMON observation identity,
not a protected-interface deletion certificate or a timed/INDEPENDENT law. -/
theorem randomizedFullForestLaw_splice {Config Copy : Type*}
    [Fintype Config] [Fintype Copy] [DecidableEq Copy]
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E)
    (heq : exposure N C r A.fragment.parents.parent0 =
      exposure N C r A.fragment.parents.parent1)
    (ν : PMF Config) (masks : Config → OriginalMask N) (sample : Copy → X) :
    randomizedFullForestLaw (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRegistry N hc b hb A H) (splicedProbabilities N hc b hb A p)
        (splicedRates N C r b A) ν (restrictMasks N hc b hb A masks) sample =
      randomizedFullForestLaw N C H p r ν masks sample := by
  rw [randomizedFullForestLaw_eq_tree_bind, randomizedFullForestLaw_eq_tree_bind,
    randomizedTreeLaw_splice N C H p hc b hb A r heq ν masks]

-- Future exact interface/axiom requests; no execution output is claimed.
#check weightedNormalize_override_splice
#check controlledFullForestLaw_splice
#check randomizedTreeLaw_splice
#check randomizedFullForestLaw_splice
#print axioms weightedNormalize_override_splice
#print axioms maskedNormalizedTree_splice
#print axioms controlledFullForestLaw_splice
#print axioms randomizedTreeLaw_splice
#print axioms randomizedFullForestLaw_splice

end Astra.PhysicalSpliceControlledLaw
