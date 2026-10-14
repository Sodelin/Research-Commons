import Astra.PhysicalSpliceWeights
import Astra.OriginalBankRestriction
import G4WeightedOrdinaryTreeLaw

/-!
# Actual COMMON source-forest laws on the constructed equal-exposure splice

Source-only composition, unselected and uncompiled. The fixed-bank law below
is the actual compiled calendar source program followed by actual ancestral
completion and the existing unranked forest observation. It is not defined by
the ordinary weighted-tree evaluator. Both law equalities are derived from
the constructed tuple and the equality of the two original arm exposures.
No mask, joint configuration, protected trace or global representative claim
is introduced in this module.
-/

namespace Astra.PhysicalSpliceCommonLaw

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ActualTwoPortBlob G1SplicedSourceAdmission
open GProgram.G7.OriginalSurvivalCoverage
open DotG4.WeightedOrdinaryTreeLaw
open Astra.PhysicalSpliceRates Astra.PhysicalSpliceRegistry
open Astra.PhysicalSpliceWeights Astra.OriginalBankRestriction
open G1CutChildPorts
open scoped Classical

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq Copy]

/-- A literal abbreviation of the actual source-program observation PMF.
The independent ordinary-tree evaluator occurs only in the theorem below. -/
noncomputable def fixedBankCommonForestLaw (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (sample : Copy → X) (coin : CommonSeed N) :
    PMF (Finset (UnrankedTree Copy)) :=
  ((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => true))
    (initialCode N sample (originalRegister N coin))).bind
      (ancestralCompletion N r (Fintype.card Copy))).map
        (fun d => sourceUnrankedForest (state d) Finset.univ)

theorem fixedBankCommonForestLaw_eq_weighted (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (sample : Copy → X) (coin : CommonSeed N) :
    fixedBankCommonForestLaw N C H p r sample coin =
      ordinaryCompletedTreeLaw (weightedNormalize N C H r coin) sample :=
  actual_common_completed_weighted_tree_law N C H p r sample coin

/-- Every complete original bank has the same actual final unranked forest
law on the constructed splice, for every finite original-copy allocation. -/
theorem fixed_bank_common_forest_splice (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (hc : CutChild N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (r : PositivePairRates E)
    (heq : exposure N C r A.fragment.parents.parent0 =
      exposure N C r A.fragment.parents.parent1)
    (sample : Copy → X) (coin : CommonSeed N) :
    fixedBankCommonForestLaw (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRegistry N hc b hb A H) (splicedProbabilities N hc b hb A p)
        (splicedRates N C r b A) sample (restrictBank N hc b hb A coin) =
      fixedBankCommonForestLaw N C H p r sample coin := by
  rw [fixedBankCommonForestLaw_eq_weighted, fixedBankCommonForestLaw_eq_weighted,
    weightedNormalize_splice N C H hc b hb A r heq coin]

/-- The actual new natural Bernoulli bank is the proved marginal of the old
one. Average complete source-program forest laws, never separate clade or
pair marginals; the representative tuple does not depend on the bank/sample. -/
theorem natural_common_forest_splice (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (hc : CutChild N) (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (r : PositivePairRates E)
    (heq : exposure N C r A.fragment.parents.parent0 =
      exposure N C r A.fragment.parents.parent1) (sample : Copy → X) :
    (originalRegisterMeasure (splicedNetwork N hc b hb A)
        (splicedProbabilities N hc b hb A p)).toPMF.bind
        (fixedBankCommonForestLaw (splicedNetwork N hc b hb A)
          (splicedCalendar N hc b hb A C) (splicedRegistry N hc b hb A H)
          (splicedProbabilities N hc b hb A p) (splicedRates N C r b A) sample) =
      (originalRegisterMeasure N p).toPMF.bind
        (fixedBankCommonForestLaw N C H p r sample) := by
  rw [← original_bank_restriction_pmf N hc b hb A p, PMF.bind_map]
  congr 1
  funext coin
  exact fixed_bank_common_forest_splice N C H p hc b hb A r heq sample coin

-- Unexecuted requests for the future exact definition/type/axiom audit.
#print fixedBankCommonForestLaw
#check fixed_bank_common_forest_splice
#check natural_common_forest_splice
#print axioms fixedBankCommonForestLaw_eq_weighted
#print axioms fixed_bank_common_forest_splice
#print axioms natural_common_forest_splice

end Astra.PhysicalSpliceCommonLaw
