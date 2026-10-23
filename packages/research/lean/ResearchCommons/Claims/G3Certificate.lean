import G4WholeProfileDetermination

/-! Supplied-certificate consumer of the retained COMMON row/moment theorem.
The hand bounded-witness result is reused, not rederived. This file supplies
its supported-bank/grid step only. It does not construct the protected
physical reduction or source-size bound, acquire a certificate, or decide NO. -/
noncomputable section
namespace ResearchCommons.Claims.G3Certificate
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.SourceNaturalInitialization
open DotG4.WholeProfileDetermination DotG4.ActualSparseCertificateExistence
open DotG4.ActualPositiveGridUniqueness
open scoped Classical BigOperators

/-- Removing zero-weight pairs preserves the SAME moment, without refitting
or normalizing any positive weight. -/
theorem supported_moment {A : Type*} [Fintype A]
    (q : PMF A) (x : A → ℝ) (k : Nat) :
    finiteBankMoment (positiveSupportPMF q) (fun a => x a.val) k =
      finiteBankMoment q x k := by
  exact positiveSupportPMF_sum q (fun a => x a ^ k.choose 2)

/-- Every supported pair is confined by the supplied nonnegative certificate.
Zero-weight configurations are not assigned an observed constraint. -/
theorem supported_atoms_in_supplied_grid {A : Type*} [Fintype A]
    (q : PMF A) (x : A → ℝ) (hx : ∀ a, 0 < x a ∧ x a ≤ 1)
    (L : Nat) (c : Nat → ℝ)
    (hne : sparsePolynomial (momentLevels L) c ≠ 0)
    (hnonneg : ∀ z ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ (sparsePolynomial (momentLevels L) c).eval z)
    (hz : (∑ k ∈ momentLevels L, c k * finiteBankMoment q x k) = 0) :
    ∀ a, q a ≠ 0 → x a ∈ positiveCertificateGrid L c := by
  have hs : (∑ k ∈ momentLevels L, c k *
      finiteBankMoment (positiveSupportPMF q) (fun a => x a.val) k) = 0 := by
    simpa only [supported_moment] using hz
  have confined := finiteBank_certificate_restricts
    (positiveSupportPMF q) (positiveSupportPMF_positive q) (fun a => x a.val)
    (fun a => hx a.val) L c hne hnonneg hs
  intro a ha
  exact confined ⟨a, ha⟩

/-- Actual finite randomized COMMON comb rows, ONE configuration/bank PMF,
and a supplied exact zero certificate imply the finite grid at every
supported pair. Strict physical source and endpoint1 are both retained.
No actual source is asserted to exist, and no bound on original graph size
is claimed by this component. -/
theorem supplied_common_rows_restrict_supported_bank
    {V E X Config : Type*}
    [Fintype V] [Fintype E] [Fintype X] [Fintype Config]
    [DecidableEq V] [DecidableEq E] [DecidableEq X]
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (ν : PMF Config) (masks : Config → OriginalMask N) (i j : X)
    (L : Nat) (c : Nat → ℝ)
    (hne : sparsePolynomial (momentLevels L) c ≠ 0)
    (hnonneg : ∀ z ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ (sparsePolynomial (momentLevels L) c).eval z)
    (hz : (∑ k ∈ momentLevels L,
      c k * randomizedLegalCombMoment N C H p r ν masks i j k) = 0) :
    (positiveCertificateGrid L c).card < L ∧
      ∀ z, configurationBankPMF ν (originalRegisterMeasure N p).toPMF z ≠ 0 →
        directedSurvival (maskedNormalizedTree N C H r (masks z.1) z.2) i j ∈
          positiveCertificateGrid L c := by
  refine ⟨positiveCertificateGrid_card_lt L c hne, ?_⟩
  apply supported_atoms_in_supplied_grid
    (configurationBankPMF ν (originalRegisterMeasure N p).toPMF)
    (fun z => directedSurvival (maskedNormalizedTree N C H r (masks z.1) z.2) i j)
    (fun z => directedSurvival_bounds _ i j) L c hne hnonneg
  calc
    (∑ k ∈ momentLevels L, c k *
      finiteBankMoment (configurationBankPMF ν (originalRegisterMeasure N p).toPMF)
        (fun z => directedSurvival (maskedNormalizedTree N C H r (masks z.1) z.2) i j) k) =
        ∑ k ∈ momentLevels L,
          c k * randomizedLegalCombMoment N C H p r ν masks i j k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [actual_randomized_legal_moment N C H p r ν masks i j k
        (momentLevels_positive L k hk)]
    _ = 0 := hz

abbrev actual_randomized_comb_moment :=
  @DotG4.WholeProfileDetermination.actual_randomized_legal_moment

abbrev supplied_positive_grid_cardinality :=
  @DotG4.ActualPositiveGridUniqueness.positiveCertificateGrid_card_lt

end ResearchCommons.Claims.G3Certificate
