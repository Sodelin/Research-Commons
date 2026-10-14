import Astra.PhysicalCommonStep
import Astra.PhysicalSpliceAffine
import Astra.BankPrefixSupport
import Astra.PositiveSupportAdapter
import G5ParentPositionPushforward

/-! Source-only natural-COMMON support budget for actual unequal cells in one
original child-cut class. The affine premise of the generic prefix lemma is
proved from the same source tuple. No desired output law or count is assumed.
This is not a protected representative theorem or a randomized-row result. -/
namespace Astra.ActualCellSupportBudget

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.OriginalFixedIDControls
open G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint
open GProgram.G7.OriginalSurvivalCoverage
open DotG4.WeightedOrdinaryTreeLaw DotG4.WholeProfileDetermination
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open Astra.PhysicalCommonStep Astra.PhysicalSpliceRegistry
open Astra.PhysicalSpliceAffine Astra.BankPrefixSupport Astra.PositiveSupportAdapter
open scoped Classical BigOperators

universe u v w
variable {X : Type w} [Fintype X] [DecidableEq X]

/-- The literal nonroot two-port predicate on actual original blobs. -/
def Cell (S : PhysicalSource.{u,v,w} X) :=
  {b : S.source.network.graph.Blob //
    b ≠ S.source.network.graph.blobOf S.source.network.root ∧
      Fintype.card (S.source.network.BlobPort b) = 2}

noncomputable def cellBigon (S : PhysicalSource.{u,v,w} X) (c : Cell S) :
    ActualBlobBigon S.source.network c.val :=
  stepBigon S c.val c.property.1 c.property.2

noncomputable def cellHybrid (S : PhysicalSource.{u,v,w} X) (c : Cell S) :
    Hybrid S.source.network := removedHybrid S.source.network c.val (cellBigon S c)

/-- Distinct original blob cells have distinct original hybrid identities. -/
theorem cellHybrid_injective (S : PhysicalSource.{u,v,w} X) :
    Function.Injective (cellHybrid S) := by
  intro c d he
  apply Subtype.ext
  calc
    c.val = S.source.network.graph.blobOf (cellHybrid S c).val :=
      (cellBigon S c).hybrid_in_blob.symm
    _ = S.source.network.graph.blobOf (cellHybrid S d).val :=
      congrArg (fun h : Hybrid S.source.network => S.source.network.graph.blobOf h.val) he
    _ = d.val := (cellBigon S d).hybrid_in_blob

noncomputable def cellCut (S : PhysicalSource.{u,v,w} X) (c : Cell S) : Finset X :=
  childCut S.source.network c.val (cellBigon S c)

/-- Original registry order is retained, even if fragment order is reversed. -/
noncomputable def armExposure (S : PhysicalSource.{u,v,w} X) (c : Cell S)
    (bit : Bool) : ℝ :=
  exposure S.source.network S.source.calendar S.rates
    ((S.registry.parents (cellHybrid S c)).parent bit)

/-- Equality of the two actual registry costs is exactly equality of the two
extracted fragment costs. Both exhaust the same original incoming occurrences. -/
theorem armExposure_eq_iff_fragment (S : PhysicalSource.{u,v,w} X) (c : Cell S) :
    armExposure S c false = armExposure S c true ↔
      EqualArmExposure S c.val c.property.1 c.property.2 := by
  let N := S.source.network
  let A := cellBigon S c
  let h := cellHybrid S c
  let cost : S.source.Edge → ℝ := exposure N S.source.calendar S.rates
  constructor
  · intro heq
    have ht0 : N.graph.target A.fragment.parents.parent0 = (S.registry.parents h).hybrid :=
      A.fragment.parents.target0.trans (S.registry.original_site h).symm
    have ht1 : N.graph.target A.fragment.parents.parent1 = (S.registry.parents h).hybrid :=
      A.fragment.parents.target1.trans (S.registry.original_site h).symm
    obtain ⟨b0, hb0⟩ := GProgram.G5.ParentCalendar.incoming_edge_is_original_parent
      (S.registry.parents h) ht0
    obtain ⟨b1, hb1⟩ := GProgram.G5.ParentCalendar.incoming_edge_is_original_parent
      (S.registry.parents h) ht1
    have hcost (bit : Bool) : cost ((S.registry.parents h).parent bit) = armExposure S c false := by
      cases bit
      · rfl
      · exact heq.symm
    change cost A.fragment.parents.parent0 = cost A.fragment.parents.parent1
    calc
      cost A.fragment.parents.parent0 = cost ((S.registry.parents h).parent b0) :=
        congrArg cost hb0.symm
      _ = armExposure S c false := hcost b0
      _ = cost ((S.registry.parents h).parent b1) := (hcost b1).symm
      _ = cost A.fragment.parents.parent1 := congrArg cost hb1
  · intro heq
    change cost A.fragment.parents.parent0 = cost A.fragment.parents.parent1 at heq
    have hcost (bit : Bool) : cost ((S.registry.parents h).parent bit) =
        cost A.fragment.parents.parent0 := by
      have ht := registry_parent_target N S.registry h bit
      rcases actual_hybrid_parents_exhaustive N c.val A
        ((S.registry.parents h).parent bit) ht with hp | hp
      · rw [hp]
      · rw [hp]
        exact heq.symm
    exact (hcost false).trans (hcost true).symm

theorem unequal_armExposure_iff (S : PhysicalSource.{u,v,w} X) (c : Cell S) :
    armExposure S c false ≠ armExposure S c true ↔
      ¬ EqualArmExposure S c.val c.property.1 c.property.2 :=
  not_congr (armExposure_eq_iff_fragment S c)

/-- This uses the existing real survival of the actual original natural bank,
not a newly fitted profile or a product of external configuration marginals. -/
noncomputable def naturalSupportValues (S : PhysicalSource.{u,v,w} X) (i j : X) : Finset ℝ :=
  positiveSupportValues (coinWeight S.source.network S.probabilities)
    (realSurvival S.source.network S.source.calendar S.registry S.probabilities S.rates i j)

lemma actual_natural_survival (S : PhysicalSource.{u,v,w} X)
    (coin : CommonSeed S.source.network) (i j : X) :
    realSurvival S.source.network S.source.calendar S.registry S.probabilities S.rates i j coin =
      Real.exp (-directedExposure
        (weightedNormalize S.source.network S.source.calendar S.registry S.rates coin) i j) := by
  have h := maskedNormalizedTree_survival S.source.network S.source.calendar S.registry
    S.probabilities S.rates (fun _ => none) coin i j
  simpa [maskedNormalizedTree, overrideBank, directedSurvival] using h.symm

lemma every_natural_bank_mem_support (S : PhysicalSource.{u,v,w} X)
    (coin : CommonSeed S.source.network) (i j : X) :
    Real.exp (-directedExposure
      (weightedNormalize S.source.network S.source.calendar S.registry S.rates coin) i j) ∈
        naturalSupportValues S i j := by
  apply Finset.mem_image.mpr
  refine ⟨coin, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · exact coinWeight_positive S.source.network S.probabilities coin
  · exact actual_natural_survival S coin i j

/-- The generic bank-flip identity is derived here from the actual affine
splice theorem. The equal-cut premise is literal finite source membership. -/
lemma cell_flip_difference (S : PhysicalSource.{u,v,w} X) (c anchor : Cell S)
    (hsame : cellCut S c = cellCut S anchor) (i j : X)
    (hi : i ∈ cellCut S anchor) (hj : j ∉ cellCut S anchor)
    (coin coin' : CommonSeed S.source.network)
    (hcoin : ∀ h, h ≠ cellHybrid S c → coin h = coin' h) :
    directedExposure (weightedNormalize S.source.network S.source.calendar S.registry
        S.rates coin') i j -
      directedExposure (weightedNormalize S.source.network S.source.calendar S.registry
        S.rates coin) i j =
      armExposure S c (coin' (cellHybrid S c)) - armExposure S c (coin (cellHybrid S c)) := by
  have h := directedExposure_bank_difference S.source.network S.source.calendar S.registry
    S.source.cutChild c.val c.property.1 (cellBigon S c) S.rates coin' coin
    (fun h hh => (hcoin h hh).symm) i j
  have hpair : i ∈ childCut S.source.network c.val (cellBigon S c) ∧
      j ∉ childCut S.source.network c.val (cellBigon S c) := by
    change i ∈ cellCut S c ∧ j ∉ cellCut S c
    rw [hsame]
    exact ⟨hi, hj⟩
  rw [if_pos hpair] at h
  exact h

/-- A fixed original-ID mask may force other sites. A counted cell must remain
natural; overriding then preserves the same exact one-site difference. -/
lemma cell_masked_flip_difference (S : PhysicalSource.{u,v,w} X) (c anchor : Cell S)
    (mask : OriginalMask S.source.network) (hnatural : mask (cellHybrid S c) = none)
    (hsame : cellCut S c = cellCut S anchor) (i j : X)
    (hi : i ∈ cellCut S anchor) (hj : j ∉ cellCut S anchor)
    (coin coin' : CommonSeed S.source.network)
    (hcoin : ∀ h, h ≠ cellHybrid S c → coin h = coin' h) :
    directedExposure (maskedNormalizedTree S.source.network S.source.calendar S.registry
        S.rates mask coin') i j -
      directedExposure (maskedNormalizedTree S.source.network S.source.calendar S.registry
        S.rates mask coin) i j =
      armExposure S c (coin' (cellHybrid S c)) - armExposure S c (coin (cellHybrid S c)) := by
  have hoc : ∀ h, h ≠ cellHybrid S c →
      overrideBank S.source.network mask coin h = overrideBank S.source.network mask coin' h := by
    intro h hh
    exact congrArg (fun bit => (mask h).getD bit) (hcoin h hh)
  have h := cell_flip_difference S c anchor hsame i j hi hj
    (overrideBank S.source.network mask coin) (overrideBank S.source.network mask coin') hoc
  simpa [maskedNormalizedTree, overrideBank, hnatural] using h

/-- Fixed-mask finite cover interface. The literal cover is supplied for this
row; no joint-configuration PMF is factored or independently sampled here. -/
theorem same_cut_masked_cover_bound (S : PhysicalSource.{u,v,w} X)
    (anchor : Cell S) {m : Nat} (cells : Fin m → Cell S)
    (hinj : Function.Injective cells)
    (hsame : ∀ k, cellCut S (cells k) = cellCut S anchor)
    (hunequal : ∀ k, ¬ EqualArmExposure S (cells k).val
      (cells k).property.1 (cells k).property.2)
    (mask : OriginalMask S.source.network)
    (hnatural : ∀ k, mask (cellHybrid S (cells k)) = none)
    (i j : X) (hi : i ∈ cellCut S anchor) (hj : j ∉ cellCut S anchor)
    (grid : Finset ℝ)
    (cover : ∀ coin : CommonSeed S.source.network,
      directedSurvival (maskedNormalizedTree S.source.network S.source.calendar S.registry
        S.rates mask coin) i j ∈ grid) :
    m + 1 ≤ grid.card := by
  let J : Fin m → Hybrid S.source.network := fun k => cellHybrid S (cells k)
  have hJ : Function.Injective J := (cellHybrid_injective S).comp hinj
  have hneq (k : Fin m) : armExposure S (cells k) false ≠ armExposure S (cells k) true :=
    (unequal_armExposure_iff S (cells k)).mpr (hunequal k)
  exact prefix_survival_card J hJ (fun k => armExposure S (cells k)) hneq
    (fun _ => false)
    (fun coin => directedExposure
      (maskedNormalizedTree S.source.network S.source.calendar S.registry S.rates mask coin) i j)
    (fun k coin coin' hc => cell_masked_flip_difference S (cells k) anchor mask (hnatural k)
      (hsame k) i j hi hj coin coin' hc)
    grid cover

/-- Every finite injective family of actual unequal cells in one child-cut
class produces m+1 distinct positive-support values in the same natural row. -/
theorem same_cut_unequal_cells_support_bound (S : PhysicalSource.{u,v,w} X)
    (anchor : Cell S) {m : Nat} (cells : Fin m → Cell S)
    (hinj : Function.Injective cells)
    (hsame : ∀ k, cellCut S (cells k) = cellCut S anchor)
    (hunequal : ∀ k, ¬ EqualArmExposure S (cells k).val
      (cells k).property.1 (cells k).property.2)
    (i j : X) (hi : i ∈ cellCut S anchor) (hj : j ∉ cellCut S anchor) :
    m + 1 ≤ (naturalSupportValues S i j).card := by
  let J : Fin m → Hybrid S.source.network := fun k => cellHybrid S (cells k)
  have hJ : Function.Injective J := (cellHybrid_injective S).comp hinj
  have hneq (k : Fin m) : armExposure S (cells k) false ≠ armExposure S (cells k) true :=
    (unequal_armExposure_iff S (cells k)).mpr (hunequal k)
  exact prefix_survival_card J hJ (fun k => armExposure S (cells k)) hneq
    (fun _ => false)
    (fun coin => directedExposure
      (weightedNormalize S.source.network S.source.calendar S.registry S.rates coin) i j)
    (fun k coin coin' hc => cell_flip_difference S (cells k) anchor (hsame k) i j hi hj
      coin coin' hc)
    (naturalSupportValues S i j) (fun coin => every_natural_bank_mem_support S coin i j)

/-- A separating original-taxon pair is derived from the actual anchor bridge. -/
theorem same_cut_support_witness (S : PhysicalSource.{u,v,w} X)
    (anchor : Cell S) {m : Nat} (cells : Fin m → Cell S)
    (hinj : Function.Injective cells)
    (hsame : ∀ k, cellCut S (cells k) = cellCut S anchor)
    (hunequal : ∀ k, ¬ EqualArmExposure S (cells k).val
      (cells k).property.1 (cells k).property.2) :
    ∃ i j : X, i ≠ j ∧ i ∈ cellCut S anchor ∧ j ∉ cellCut S anchor ∧
      m + 1 ≤ (naturalSupportValues S i j).card := by
  obtain ⟨i, j, hi, hj, hij⟩ := Astra.BridgeTaxonCuts.bridgeTaxa_separating_pair S.source.network
    ⟨(cellBigon S anchor).child, (cellBigon S anchor).child_bridge⟩
  exact ⟨i, j, hij, hi, hj,
    same_cut_unequal_cells_support_bound S anchor cells hinj hsame hunequal i j hi hj⟩

/-- Conditional supplied-certificate count for this exact natural row. Exact
coefficient/exponent identity, nonzero evaluation, nonnegativity, and literal
bank-weighted annihilation are retained. No bound or unknown source is input. -/
theorem supplied_certificate_same_cut_cell_bound (S : PhysicalSource.{u,v,w} X)
    (anchor : Cell S) {m : Nat} (cells : Fin m → Cell S)
    (hinj : Function.Injective cells)
    (hsame : ∀ k, cellCut S (cells k) = cellCut S anchor)
    (hunequal : ∀ k, ¬ EqualArmExposure S (cells k).val
      (cells k).property.1 (cells k).property.2)
    (i j : X) (hi : i ∈ cellCut S anchor) (hj : j ∉ cellCut S anchor)
    (L : Nat) (coeff : Nat → ℝ) (poly : ℝ → ℝ)
    (identity : ∀ x, poly x = (sparsePolynomial (momentLevels L) coeff).eval x)
    (testPoint : ℝ) (nonzero : poly testPoint ≠ 0)
    (nonnegative : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ poly x)
    (annihilation : ∑ coin : CommonSeed S.source.network,
      coinWeight S.source.network S.probabilities coin *
        poly (realSurvival S.source.network S.source.calendar S.registry
          S.probabilities S.rates i j coin) = 0) :
    m ≤ L - 2 := by
  have hlo := same_cut_unequal_cells_support_bound S anchor cells hinj hsame hunequal i j hi hj
  have hhi := supplied_certificate_support_bound L coeff poly identity testPoint nonzero
    (coinWeight S.source.network S.probabilities)
    (realSurvival S.source.network S.source.calendar S.registry S.probabilities S.rates i j)
    (fun coin => (coinWeight_positive S.source.network S.probabilities coin).le)
    (fun coin _ => ⟨realSurvival_positive S.source.network S.source.calendar S.registry
      S.probabilities S.rates i j coin, realSurvival_le_one S.source.network S.source.calendar
      S.registry S.probabilities S.rates i j coin⟩)
    nonnegative annihilation
  change (naturalSupportValues S i j).card ≤ L - 1 at hhi
  omega

#print axioms cellHybrid_injective
#print axioms armExposure_eq_iff_fragment
#print axioms cell_flip_difference
#print axioms cell_masked_flip_difference
#print axioms same_cut_masked_cover_bound
#print axioms same_cut_unequal_cells_support_bound
#print axioms supplied_certificate_same_cut_cell_bound

end Astra.ActualCellSupportBudget
