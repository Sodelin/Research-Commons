import G4WholeProfileDetermination
import Astra.PositiveSupportAdapter

/-!
# Supplied certificates on actual randomized legal COMMON rows

Source candidate, not compiled or accepted as a new Lean execution result.
The original selected providers are imported in full. A certificate supplies
only coefficients, moments, nonnegativity and a concrete nonzero evaluation;
the source is universally quantified as a compatible realizer, not acquired
or assumed as a field of the executable input.

The same original network, calendar, parent registry, rates, inheritance
parameters, full configuration PMF and masks serve every queried level.
No source, original ID, mask or protected-coordinate record is transformed.
Correlations between mask sites stay inside the one configuration draw.
The imported randomizedLegalCombMoment fixes the padded sample/pruning/event
and exact combCoefficient normalization. This does not certify an external
parser or a change of encoding. No physical representative, hybrid budget,
source existence, future-law equality or arbitrary-input G3 decision follows.
-/

namespace Astra.ActualLegalRowSupport

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.OriginalFixedIDControls
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open DotG4.WholeProfileDetermination
open Astra.PositiveSupportAdapter
open scoped Classical BigOperators ENNReal

variable {V E X Config : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Config]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]

/-- Keep the whole supplied configuration draw, then the original natural bank.
This is not a product of individual forcing-site marginals. -/
noncomputable def jointBankWeight (N : RootedBinary V E X)
    (p : HybridProbabilities N) (ν : PMF Config) : Config × CommonSeed N → ℝ :=
  fun z => (configurationBankPMF ν (originalRegisterMeasure N p).toPMF z).toReal

/-- Directed survival in the actual masked normalized tree, on original taxa.
The original masks and one physical tuple are retained unchanged. -/
noncomputable def jointDirectedSurvival (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (masks : Config → OriginalMask N) (i j : X) : Config × CommonSeed N → ℝ :=
  fun z => directedSurvival (maskedNormalizedTree N C H r (masks z.1) z.2) i j

/-- Exact supplied row matching yields zero certificate expectation on the
actual joint bank. Neither source existence nor the desired support bound is
an input. The coefficients, moments and physical inputs are fixed across k. -/
theorem actual_rows_certificate_annihilates
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (ν : PMF Config) (masks : Config → OriginalMask N) (i j : X)
    (L : Nat) (coeff moments : Nat → ℝ)
    (rows : ∀ k ∈ momentLevels L,
      randomizedLegalCombMoment N C H p r ν masks i j k = moments k)
    (certificate : (∑ k ∈ momentLevels L, coeff k * moments k) = 0) :
    (∑ z : Config × CommonSeed N, jointBankWeight N p ν z *
      (sparsePolynomial (momentLevels L) coeff).eval
        (jointDirectedSurvival N C H r masks i j z)) = 0 := by
  let ρ : PMF (Config × CommonSeed N) :=
    configurationBankPMF ν (originalRegisterMeasure N p).toPMF
  let x : Config × CommonSeed N → ℝ := jointDirectedSurvival N C H r masks i j
  have hm (k : Nat) (hk : k ∈ momentLevels L) :
      finiteBankMoment ρ x k = moments k := by
    exact (actual_randomized_legal_moment N C H p r ν masks i j k
      (momentLevels_positive L k hk)).symm.trans (rows k hk)
  have hz : (∑ k ∈ momentLevels L, coeff k * finiteBankMoment ρ x k) = 0 := by
    calc
      _ = ∑ k ∈ momentLevels L, coeff k * moments k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hm k hk]
      _ = 0 := certificate
  rw [finiteBankMoment_polynomial] at hz
  simpa only [ρ, x, jointBankWeight] using hz

/-- Bound distinct positive-mass actual survivals from the supplied polynomial.
The survival endpoint 1 is included, repeated values count once, and zero-mass
joint configurations are excluded. No representative or future-law assertion
is added to the imported arithmetic/support result. -/
theorem actual_rows_positive_support_bound
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (ν : PMF Config) (masks : Config → OriginalMask N) (i j : X)
    (L : Nat) (coeff moments : Nat → ℝ)
    (testPoint : ℝ)
    (nonzero : (sparsePolynomial (momentLevels L) coeff).eval testPoint ≠ 0)
    (nonnegative : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ (sparsePolynomial (momentLevels L) coeff).eval x)
    (rows : ∀ k ∈ momentLevels L,
      randomizedLegalCombMoment N C H p r ν masks i j k = moments k)
    (certificate : (∑ k ∈ momentLevels L, coeff k * moments k) = 0) :
    (positiveSupportValues (jointBankWeight N p ν)
      (jointDirectedSurvival N C H r masks i j)).card ≤ L - 1 := by
  apply supplied_certificate_support_bound L coeff
    (fun x => (sparsePolynomial (momentLevels L) coeff).eval x)
    (fun _ => rfl) testPoint nonzero
    (jointBankWeight N p ν) (jointDirectedSurvival N C H r masks i j)
  · intro z
    exact ENNReal.toReal_nonneg
  · intro z _
    exact directedSurvival_bounds (maskedNormalizedTree N C H r (masks z.1) z.2) i j
  · exact nonnegative
  · exact actual_rows_certificate_annihilates N C H p r ν masks i j L coeff moments
      rows certificate

#print axioms actual_rows_certificate_annihilates
#print axioms actual_rows_positive_support_bound

end Astra.ActualLegalRowSupport
