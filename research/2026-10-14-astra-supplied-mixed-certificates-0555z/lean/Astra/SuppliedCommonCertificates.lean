import G4WholeProfileDetermination
import G4ActualPositiveGridUniqueness

/-!
Source-only standalone composition of the available selected certificate
providers. The record and mixed-support proof are adapted, with credit, from
dot's G3CertifiedCommonBoundedWitness (400153aa...), whose sole import's exact
0616... body is unavailable here. This file does not replace or authenticate
that missing physical provider, and asserts no bounded representative result.
No unknown actual target is a field of the supplied input record.
-/
namespace Astra.SuppliedCommonCertificates

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.OriginalFixedIDControls
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open DotG4.ActualPositiveGridUniqueness DotG4.WeightedOrdinaryTreeLaw
open DotG4.WholeProfileDetermination
open scoped Classical BigOperators ENNReal

universe w q

/-- Literal supplied normalized moment values, coefficients and exact proof
obligations; no realizing source, source-size bound or certificate search. -/
structure SuppliedCombCertificates (Y : Type w) where
  level : Y × Y → Nat
  value : Y × Y → Nat → ℝ
  coeff : Y × Y → Nat → ℝ
  level_pos : ∀ ij, 0 < level ij
  nonzero : ∀ ij, sparsePolynomial (momentLevels (level ij)) (coeff ij) ≠ 0
  nonnegative : ∀ ij x, x ∈ Set.Icc (0 : ℝ) 1 →
    0 ≤ (sparsePolynomial (momentLevels (level ij)) (coeff ij)).eval x
  annihilates : ∀ ij,
    (∑ k ∈ momentLevels (level ij), coeff ij k * value ij k) = 0

variable {Y : Type w} [Fintype Y] [DecidableEq Y]

noncomputable def certificateGrid (cert : SuppliedCombCertificates Y)
    (ij : Y × Y) : Finset ℝ :=
  positiveCertificateGrid (cert.level ij) (cert.coeff ij)

noncomputable def supportCap (cert : SuppliedCombCertificates Y) : Nat :=
  (Finset.univ : Finset (Y × Y)).sup (fun ij => cert.level ij - 1)

noncomputable def hybridBudget (cert : SuppliedCombCertificates Y) (h : Nat) : Nat :=
  (2 * Fintype.card Y - 2 + 2*h) +
    (8 * Fintype.card Y - 8 + 6*h) * (supportCap cert - 1)

lemma certificateGrid_card_le (cert : SuppliedCombCertificates Y) (ij : Y × Y) :
    (certificateGrid cert ij).card ≤ supportCap cert := by
  have hlt := positiveCertificateGrid_card_lt (cert.level ij) (cert.coeff ij)
    (cert.nonzero ij)
  have hle : (certificateGrid cert ij).card ≤ cert.level ij - 1 := by
    dsimp only [certificateGrid]
    omega
  exact hle.trans (Finset.le_sup (f := fun ij => cert.level ij - 1) (Finset.mem_univ ij))

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Every bank in every supported whole configuration lies in the original
certificate grid. Zero-weight configurations receive no root assertion.
The universally quantified source is a possible realizer, not an input field
asserting existence. Protection/admission are not used in this support lemma. -/
theorem actual_mixed_certificate_support (cert : SuppliedCombCertificates Y)
    (N : RootedBinary V E Y) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    {Config : Type q} [Fintype Config] (ν : PMF Config)
    (masks : Config → OriginalMask N)
    (hmatch : ∀ i j k, k ∈ momentLevels (cert.level (i,j)) →
      randomizedLegalCombMoment N C H p r ν masks i j k = cert.value (i,j) k) :
    ∀ cfg, ν cfg ≠ 0 → ∀ coin i j,
      realSurvival N C H p r i j (overrideBank N (masks cfg) coin) ∈
        certificateGrid cert (i,j) := by
  intro cfg hcfg coin i j
  let ρ := configurationBankPMF ν (originalRegisterMeasure N p).toPMF
  let x : Config × CommonSeed N → ℝ := fun s =>
    directedSurvival (maskedNormalizedTree N C H r (masks s.1) s.2) i j
  have hm (k : Nat) (hk : k ∈ momentLevels (cert.level (i,j))) :
      finiteBankMoment (positiveSupportPMF ρ) (fun s => x s.val) k = cert.value (i,j) k := by
    change (∑ s : {s : Config × CommonSeed N // ρ s ≠ 0},
      (positiveSupportPMF ρ s).toReal * x s.val ^ k.choose 2) = _
    rw [positiveSupportPMF_sum ρ (fun s => x s ^ k.choose 2)]
    have hr : randomizedLegalCombMoment N C H p r ν masks i j k = finiteBankMoment ρ x k :=
      actual_randomized_legal_moment N C H p r ν masks i j k (momentLevels_positive _ k hk)
    exact hr.symm.trans (hmatch i j k hk)
  have hz : (∑ k ∈ momentLevels (cert.level (i,j)),
      cert.coeff (i,j) k * finiteBankMoment (positiveSupportPMF ρ) (fun s => x s.val) k) = 0 := by
    calc
      _ = ∑ k ∈ momentLevels (cert.level (i,j)), cert.coeff (i,j) k * cert.value (i,j) k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hm k hk]
      _ = 0 := cert.annihilates (i,j)
  have hrestrict := finiteBank_certificate_restricts (positiveSupportPMF ρ)
    (positiveSupportPMF_positive ρ) (fun s => x s.val)
    (fun s => directedSurvival_bounds _ _ _) (cert.level (i,j)) (cert.coeff (i,j))
    (cert.nonzero (i,j)) (cert.nonnegative (i,j)) hz
  have hb : (originalRegisterMeasure N p).toPMF coin ≠ 0 := by
    intro he
    have hp := original_bank_real_weight_positive N p coin
    simp only [he, ENNReal.toReal_zero] at hp
    exact lt_irrefl _ hp
  have hpair : ρ (cfg,coin) ≠ 0 := by
    dsimp only [ρ]
    rw [configurationBankPMF_apply]
    exact mul_ne_zero hcfg hb
  have hg := hrestrict ⟨(cfg,coin), hpair⟩
  simpa only [x, certificateGrid, maskedNormalizedTree_survival N C H p r (masks cfg) coin i j]
    using hg

/-- One supported configuration is chosen within the proof; all its original
banks are covered. No independence assumption on ν or new observed row occurs. -/
theorem one_supported_configuration (cert : SuppliedCombCertificates Y)
    (N : RootedBinary V E Y) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    {Config : Type q} [Fintype Config] (ν : PMF Config)
    (masks : Config → OriginalMask N)
    (hmatch : ∀ i j k, k ∈ momentLevels (cert.level (i,j)) →
      randomizedLegalCombMoment N C H p r ν masks i j k = cert.value (i,j) k) :
    ∃ cfg, ν cfg ≠ 0 ∧ ∀ coin i j,
      realSurvival N C H p r i j (overrideBank N (masks cfg) coin) ∈
        certificateGrid cert (i,j) := by
  obtain ⟨cfg, hcfg⟩ := ν.support_nonempty
  exact ⟨cfg, hcfg, actual_mixed_certificate_support cert N C H p r ν masks hmatch cfg hcfg⟩

#print SuppliedCombCertificates
#print axioms certificateGrid_card_le
#print axioms actual_mixed_certificate_support
#print axioms one_supported_configuration

end Astra.SuppliedCommonCertificates
