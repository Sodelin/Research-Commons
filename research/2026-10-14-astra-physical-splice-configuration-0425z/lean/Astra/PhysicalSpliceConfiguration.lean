import Astra.OriginalBankRestriction
import G4WholeProfileDetermination

/-!
# Whole-configuration and original-mask transport through the splice

Source-only proposal: no elaboration, actual type/axiom audit or Lake receipt.
The supplied configuration PMF is used literally. Only its paired original
COMMON bank is restricted; configuration-site marginals are never multiplied.
The mask identities use the existing Option-valued original-ID override.
No physical output-law, protected-interface or bounded representative theorem
is assumed or asserted here.
-/

namespace Astra.PhysicalSpliceConfiguration

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.OriginalFixedIDControls
open G1ActualTwoPortBlob G1SplicedSourceAdmission
open DotG4.WeightedOrdinaryTreeLaw DotG4.WholeProfileDetermination
open Astra.PhysicalSpliceRegistry Astra.OriginalBankRestriction
open scoped Classical

/-- Map only the bank component. This equality is derived for the existing
configuration/bank constructor, with exactly the same whole configuration PMF.
It does not assume a desired marginal or factor the configuration itself. -/
lemma configurationBankPMF_map_bank
    {Config Bank ReducedBank : Type*}
    [Fintype Config] [Fintype Bank] [Fintype ReducedBank]
    (ν : PMF Config) (q : PMF Bank) (f : Bank → ReducedBank) :
    (configurationBankPMF ν q).map (fun z => (z.1, f z.2)) =
      configurationBankPMF ν (q.map f) := by
  simp only [configurationBankPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- The final source instance uses the actual bank pushforward derived in
0410, not a bank-law equality supplied by the caller. No configuration atom
is removed or renormalized, including atoms of mass zero. -/
theorem configuration_bank_restriction_pmf {Config : Type*} [Fintype Config]
    (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (p : HybridProbabilities N) (ν : PMF Config) :
    (configurationBankPMF ν (originalRegisterMeasure N p).toPMF).map
        (fun z => (z.1, restrictBank N hc b hb A z.2)) =
      configurationBankPMF ν
        (originalRegisterMeasure (splicedNetwork N hc b hb A)
          (splicedProbabilities N hc b hb A p)).toPMF := by
  rw [configurationBankPMF_map_bank, original_bank_restriction_pmf]

/-- Pull back the complete original mask along the actual retained-hybrid
injection. None stays natural; some false/true retains its original arm bit.
External protected-label/trace admissibility is a separate obligation. -/
noncomputable def restrictMask (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mask : OriginalMask N) : OriginalMask (splicedNetwork N hc b hb A) :=
  fun h => mask (retainedHybrid N hc b hb A h)

@[simp] lemma restrictMask_apply (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mask : OriginalMask N) (h : Hybrid (splicedNetwork N hc b hb A)) :
    restrictMask N hc b hb A mask h = mask (retainedHybrid N hc b hb A h) := rfl

/-- The existing override is Option.getD on the same original bank coordinate.
Both natural and forced cases commute with the literal restriction. -/
theorem overrideBank_restrict (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mask : OriginalMask N) (coin : CommonSeed N) :
    restrictBank N hc b hb A (overrideBank N mask coin) =
      overrideBank (splicedNetwork N hc b hb A) (restrictMask N hc b hb A mask)
        (restrictBank N hc b hb A coin) := by
  funext h
  change (mask (retainedHybrid N hc b hb A h)).getD
      (coin (retainedHybrid N hc b hb A h)) =
    (mask (retainedHybrid N hc b hb A h)).getD
      (coin (retainedHybrid N hc b hb A h))
  cases mask (retainedHybrid N hc b hb A h) <;> rfl

/-- Every whole configuration retains its original identity and its same
Option-valued mask at each retained original site. -/
noncomputable def restrictMasks {Config : Type*}
    (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (masks : Config → OriginalMask N) :
    Config → OriginalMask (splicedNetwork N hc b hb A) :=
  fun cfg => restrictMask N hc b hb A (masks cfg)

@[simp] lemma restrictMasks_apply {Config : Type*}
    (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (masks : Config → OriginalMask N) (cfg : Config)
    (h : Hybrid (splicedNetwork N hc b hb A)) :
    restrictMasks N hc b hb A masks cfg h = masks cfg (retainedHybrid N hc b hb A h) := rfl

theorem overrideBank_restrict_config {Config : Type*}
    (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (masks : Config → OriginalMask N) (cfg : Config) (coin : CommonSeed N) :
    restrictBank N hc b hb A (overrideBank N (masks cfg) coin) =
      overrideBank (splicedNetwork N hc b hb A) (restrictMasks N hc b hb A masks cfg)
        (restrictBank N hc b hb A coin) := by
  exact overrideBank_restrict N hc b hb A (masks cfg) coin

-- Future explicit type/axiom audit requests; no output is claimed here.
#check configuration_bank_restriction_pmf
#check restrictMasks_apply
#check overrideBank_restrict_config
#print axioms configurationBankPMF_map_bank
#print axioms configuration_bank_restriction_pmf
#print axioms restrictMask_apply
#print axioms overrideBank_restrict
#print axioms restrictMasks_apply
#print axioms overrideBank_restrict_config

end Astra.PhysicalSpliceConfiguration
