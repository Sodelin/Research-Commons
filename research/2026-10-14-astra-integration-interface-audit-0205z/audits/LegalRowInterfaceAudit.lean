import AstraLegalRowSupport

/-!
Source-only audit of the selected legal-row composition, not a replacement
provider or an execution receipt. Each example checks an existing definition
or full theorem interface; no source-existence or support-bound premise is added.
-/
set_option autoImplicit false

namespace Astra.IntegrationInterfaceAudit.LegalRows

open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.OriginalFixedIDControls
open GProgram.G2.LiteralTimedObservationPruning
open DotG4.ActualLegalPanelComb DotG34.SpecifiedCombEvent
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open DotG4.WholeProfileDetermination
open Astra.PositiveSupportAdapter Astra.ActualLegalRowSupport
open scoped Classical BigOperators ENNReal

universe uV uE uX uConfig
variable {V : Type uV} {E : Type uE} {X : Type uX} {Config : Type uConfig}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Config]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]

-- One whole configuration draw, followed by the same original natural bank.
example (N : RootedBinary V E X) (p : HybridProbabilities N)
    (ν : PMF Config) (z : Config × CommonSeed N) :
    jointBankWeight N p ν z =
      (configurationBankPMF ν (originalRegisterMeasure N p).toPMF z).toReal := rfl

example (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (masks : Config → OriginalMask N) (i j : X) (z : Config × CommonSeed N) :
    jointDirectedSurvival N C H r masks i j z =
      directedSurvival (maskedNormalizedTree N C H r (masks z.1) z.2) i j := rfl

-- Bind the actual padded allocation, passive forest pruning, labelled comb,
-- direction i,j and exact normalization. This is not an external parser proof.
example (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ν : PMF Config)
    (masks : Config → OriginalMask N) (i j : X) (k : Nat) :
    randomizedLegalCombMoment N C H p r ν masks i j k =
      (((randomizedFullForestLaw N C H p r ν masks (paddedSample k i j)).map
        (pruneForest (paddedKeep k)))
          {toUnranked (comb (paddedB (X := X) k).val ((paddedA k).map Subtype.val))}).toReal /
            combCoefficient k := rfl

example (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ν : PMF Config)
    (masks : Config → OriginalMask N) (i j : X)
    (L : Nat) (coeff moments : Nat → ℝ)
    (rows : ∀ k ∈ momentLevels L,
      randomizedLegalCombMoment N C H p r ν masks i j k = moments k)
    (certificate : (∑ k ∈ momentLevels L, coeff k * moments k) = 0) :
    (∑ z : Config × CommonSeed N, jointBankWeight N p ν z *
      (sparsePolynomial (momentLevels L) coeff).eval
        (jointDirectedSurvival N C H r masks i j z)) = 0 :=
  actual_rows_certificate_annihilates N C H p r ν masks i j L coeff moments rows certificate

-- The same tuple, masks and PMF occur outside the level quantifier. The only
-- cardinality statement is the conclusion, about DISTINCT positive-mass values.
example (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (ν : PMF Config)
    (masks : Config → OriginalMask N) (i j : X)
    (L : Nat) (coeff moments : Nat → ℝ) (testPoint : ℝ)
    (nonzero : (sparsePolynomial (momentLevels L) coeff).eval testPoint ≠ 0)
    (nonnegative : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ (sparsePolynomial (momentLevels L) coeff).eval x)
    (rows : ∀ k ∈ momentLevels L,
      randomizedLegalCombMoment N C H p r ν masks i j k = moments k)
    (certificate : (∑ k ∈ momentLevels L, coeff k * moments k) = 0) :
    (positiveSupportValues (jointBankWeight N p ν)
      (jointDirectedSurvival N C H r masks i j)).card ≤ L - 1 :=
  actual_rows_positive_support_bound N C H p r ν masks i j L coeff moments
    testPoint nonzero nonnegative rows certificate

end Astra.IntegrationInterfaceAudit.LegalRows

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.notation false
set_option pp.proofs false

#print Astra.ActualLegalRowSupport.jointBankWeight
#print Astra.ActualLegalRowSupport.jointDirectedSurvival
#print DotG4.WholeProfileDetermination.configurationBankPMF
#print DotG4.WholeProfileDetermination.randomizedLegalCombMoment
#print DotG4.WholeProfileDetermination.combCoefficient
#print DotG4.ActualLegalPanelComb.paddedSample
#print DotG4.ActualLegalPanelComb.paddedKeep
#print DotG4.ActualLegalPanelComb.paddedB
#print DotG4.ActualLegalPanelComb.paddedA
#check @Astra.ActualLegalRowSupport.actual_rows_certificate_annihilates
#check @Astra.ActualLegalRowSupport.actual_rows_positive_support_bound
#check @DotG4.WholeProfileDetermination.actual_randomized_legal_moment
#check @DotG4.WholeProfileDetermination.finiteBankMoment_polynomial
#check @DotG4.WholeProfileDetermination.directedSurvival_bounds
#print axioms Astra.ActualLegalRowSupport.actual_rows_certificate_annihilates
#print axioms Astra.ActualLegalRowSupport.actual_rows_positive_support_bound
#print axioms DotG4.WholeProfileDetermination.actual_randomized_legal_moment
#print axioms DotG4.WholeProfileDetermination.finiteBankMoment_polynomial
#print axioms DotG4.WholeProfileDetermination.directedSurvival_bounds
