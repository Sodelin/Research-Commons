import Astra.PhysicalSpliceWeights
import Astra.BridgeTaxonCuts
import G4WholeProfileDetermination

/-! Source-only affine identity for unequal arms of one actual original bigon.
The base splice is the existing fixed fragment-parent0 construction. It does
not depend on the deleted bank bit and is not asserted to preserve laws when
arms differ. All differences below are real exposure differences. -/
namespace Astra.PhysicalSpliceAffine

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open GProgram.G5.AttainedChronology
open G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph G1SplicedSourceAdmission
open GProgram.G7.OriginalSurvivalCoverage
open DotG4.WeightedOrdinaryTreeLaw DotG4.WholeProfileDetermination
open Astra.PhysicalSpliceRates Astra.PhysicalSpliceRegistry
open Astra.PhysicalSpliceClades Astra.PhysicalSpliceWeights Astra.BridgeTaxonCuts
open scoped Classical BigOperators

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]

/-- The literal original registry choice, without identifying its Boolean
order with the separately extracted fragment's parent order. -/
noncomputable def chosenArm (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (coin : CommonSeed N) : E :=
  (H.parents (removedHybrid N b A)).parent (coin (removedHybrid N b A))

noncomputable def childCut (N : RootedBinary V E X)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) : Finset X :=
  bridgeTaxa N ⟨A.child, A.child_bridge⟩

/-- One fixed physical base tuple, evaluated at the restricted original bank. -/
noncomputable def baseProfile (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (hc : CutChild N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E) (coin : CommonSeed N) : CladeWeights X :=
  weightedNormalize (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
    (splicedRegistry N hc b hb A H) (splicedRates N C r b A)
    (restrictBank N hc b hb A coin)

lemma chosenArm_eq_of_kept (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (coin : CommonSeed N)
    (e : E) (ht : N.graph.target e = A.fragment.parents.hybrid)
    (hk : (commonSwitching N H coin).keep e) : chosenArm N H b A coin = e := by
  exact ((N.switchingOfChoices_keep_at_hybrid
    (fun h => ⟨(H.parents h).parent (coin h), registry_parent_target N H h (coin h)⟩)
    (removedHybrid N b A) e ht).mp hk).symm

lemma child_edgeTaxa (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (coin : CommonSeed N) : edgeTaxa N C H coin A.child = childCut N b A :=
  common_edgeTaxa_eq_bridgeTaxa N C H coin ⟨A.child, A.child_bridge⟩

/-- The four removed occurrences contribute exactly the entry, child and
actually chosen registry arm, all on the same original child cut. -/
lemma removed_contribution (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (hc : CutChild N) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (r : PositivePairRates E) (coin : CommonSeed N)
    (D : Finset X) (hD : D ≠ ∅) :
    let f : E → ℝ≥0 := fun e =>
      if edgeTaxa N C H coin e = D then edgeExposure N C r e else 0
    f A.entry + f A.child + f A.fragment.parents.parent0 +
        f A.fragment.parents.parent1 =
      if childCut N b A = D then
        edgeExposure N C r A.entry + edgeExposure N C r A.child +
          edgeExposure N C r (chosenArm N H b A coin)
      else 0 := by
  have hED : (∅ : Finset X) ≠ D := Ne.symm hD
  have he := entry_edgeTaxa_eq_child N C H hc b A coin
  have hc' := child_edgeTaxa N C H b A coin
  rcases exactly_one_arm_kept N b A (commonSwitching N H coin) with
    ⟨hk0, hn1⟩ | ⟨hk1, hn0⟩
  · have hp := kept_parent_edgeTaxa_eq_child N C H b A coin false hk0
    have hz := edgeTaxa_empty_of_not_kept N C H coin A.fragment.parents.parent1 hn1
    have hchosen := chosenArm_eq_of_kept N H b A coin
      A.fragment.parents.parent0 A.fragment.parents.target0 hk0
    dsimp only
    rw [he, hp, hz, hc', hchosen]
    by_cases hd : childCut N b A = D <;>
      simp only [hd, if_true, if_false, if_neg hED, add_zero, zero_add]
  · have hp := kept_parent_edgeTaxa_eq_child N C H b A coin true hk1
    have hz := edgeTaxa_empty_of_not_kept N C H coin A.fragment.parents.parent0 hn0
    have hchosen := chosenArm_eq_of_kept N H b A coin
      A.fragment.parents.parent1 A.fragment.parents.target1 hk1
    dsimp only
    rw [he, hp, hz, hc', hchosen]
    by_cases hd : childCut N b A = D <;>
      simp only [hd, if_true, if_false, if_neg hED, add_zero, zero_add]

/-- Subtraction-free finite balance, before coercion to real exposures. -/
lemma weightedNormalize_balance (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (hc : CutChild N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E) (coin : CommonSeed N) (D : Finset X)
    (hD : ¬ (D = ∅ ∨ D = Finset.univ)) :
    weightedNormalize N C H r coin D +
        (if childCut N b A = D then edgeExposure N C r A.fragment.parents.parent0 else 0) =
      baseProfile N C H hc b hb A r coin D +
        (if childCut N b A = D then edgeExposure N C r (chosenArm N H b A coin) else 0) := by
  let oldf : E → ℝ≥0 := fun e =>
    if edgeTaxa N C H coin e = D then edgeExposure N C r e else 0
  let newf : SplicedEdge N b A → ℝ≥0 := fun e =>
    if edgeTaxa (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRegistry N hc b hb A H) (restrictBank N hc b hb A coin) e = D
    then edgeExposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRates N C r b A) e else 0
  have hret : (∑ e : RetainedEdge N b A, newf (.inl e)) =
      ∑ e : RetainedEdge N b A, oldf e.val := by
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [newf, oldf]
    rw [retained_edgeTaxa N C H hc b hb A coin e,
      retained_edgeExposure N hc b hb A C r e]
  have hnew : newf (.inr ()) =
      if childCut N b A = D then
        edgeExposure N C r A.entry + edgeExposure N C r A.fragment.parents.parent0 +
          edgeExposure N C r A.child else 0 := by
    dsimp only [newf]
    rw [new_edgeTaxa N C H hc b hb A coin, new_edgeExposure N hc b hb A C r,
      child_edgeTaxa N C H b A coin]
  have hremoved := removed_contribution N C H hc b A r coin D
    (fun h => hD (Or.inl h))
  have hold : (∑ e : E, oldf e) =
      (∑ e : RetainedEdge N b A, oldf e.val) +
        (if childCut N b A = D then
          edgeExposure N C r A.entry + edgeExposure N C r A.child +
            edgeExposure N C r (chosenArm N H b A coin) else 0) := by
    calc
      _ = (∑ e : RetainedEdge N b A, oldf e.val) +
          (oldf A.entry + oldf A.child + oldf A.fragment.parents.parent0 +
            oldf A.fragment.parents.parent1) := by
        simpa only [add_assoc] using sum_retained_and_four_removed N b A oldf
      _ = _ := by rw [show oldf A.entry + oldf A.child +
          oldf A.fragment.parents.parent0 + oldf A.fragment.parents.parent1 = _ from hremoved]
  have hsum : (∑ e : SplicedEdge N b A, newf e) =
      (∑ e : RetainedEdge N b A, oldf e.val) +
        (if childCut N b A = D then
          edgeExposure N C r A.entry + edgeExposure N C r A.fragment.parents.parent0 +
            edgeExposure N C r A.child else 0) := by
    rw [Fintype.sum_sum_type, Fintype.sum_unique, hret, hnew]
  simp only [weightedNormalize, baseProfile, if_neg hD]
  change (∑ e : E, oldf e) + _ = (∑ e : SplicedEdge N b A, newf e) + _
  rw [hold, hsum]
  by_cases hd : childCut N b A = D <;> simp only [hd, if_true, if_false]
  · ac_rfl
  · simp only [add_zero]

/-- Exact affine profile identity, including zero empty/full coordinates.
The physical base tuple stays fixed; a negative increment is allowed in ℝ. -/
theorem weightedNormalize_affine (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (hc : CutChild N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E) (coin : CommonSeed N) (D : Finset X) :
    (weightedNormalize N C H r coin D : ℝ) =
      (baseProfile N C H hc b hb A r coin D : ℝ) +
        if D = childCut N b A then
          exposure N C r (chosenArm N H b A coin) -
            exposure N C r A.fragment.parents.parent0 else 0 := by
  by_cases hD : D = ∅ ∨ D = Finset.univ
  · have hne : D ≠ childCut N b A := by
      rcases hD with hD | hD
      · intro he
        exact (bridgeTaxa_nonempty N ⟨A.child, A.child_bridge⟩).ne_empty (he.symm.trans hD)
      · intro he
        exact bridgeTaxa_proper N ⟨A.child, A.child_bridge⟩ (he.symm.trans hD)
    simp only [weightedNormalize, baseProfile, if_pos hD, if_neg hne,
      NNReal.coe_zero, zero_add]
  · have hbalance := weightedNormalize_balance N C H hc b hb A r coin D hD
    by_cases hd : childCut N b A = D
    · simp only [if_pos hd] at hbalance
      have hreal := congrArg (fun x : ℝ≥0 => (x : ℝ)) hbalance
      simp only [NNReal.coe_add] at hreal
      change (weightedNormalize N C H r coin D : ℝ) +
          exposure N C r A.fragment.parents.parent0 =
        (baseProfile N C H hc b hb A r coin D : ℝ) +
          exposure N C r (chosenArm N H b A coin) at hreal
      rw [if_pos hd.symm]
      linarith
    · simp only [if_neg hd, add_zero] at hbalance
      rw [if_neg (Ne.symm hd), add_zero]
      exact congrArg (fun x : ℝ≥0 => (x : ℝ)) hbalance

lemma restrictBank_eq_of_agree_off_removed (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (coin coin' : CommonSeed N)
    (hcoin : ∀ h, h ≠ removedHybrid N b A → coin h = coin' h) :
    restrictBank N hc b hb A coin = restrictBank N hc b hb A coin' := by
  funext h
  exact hcoin (retainedHybrid N hc b hb A h) (retainedHybrid_ne_removed N hc b hb A h)

/-- Changing only the removed hybrid changes exactly its actual cut coordinate. -/
theorem weightedNormalize_bank_difference (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (hc : CutChild N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E) (coin coin' : CommonSeed N)
    (hcoin : ∀ h, h ≠ removedHybrid N b A → coin h = coin' h) (D : Finset X) :
    (weightedNormalize N C H r coin D : ℝ) - (weightedNormalize N C H r coin' D : ℝ) =
      if D = childCut N b A then
        exposure N C r (chosenArm N H b A coin) - exposure N C r (chosenArm N H b A coin')
      else 0 := by
  have hbase : baseProfile N C H hc b hb A r coin = baseProfile N C H hc b hb A r coin' := by
    unfold baseProfile
    rw [restrictBank_eq_of_agree_off_removed N hc b hb A coin coin' hcoin]
  rw [weightedNormalize_affine N C H hc b hb A r coin D,
    weightedNormalize_affine N C H hc b hb A r coin' D, hbase]
  by_cases hd : D = childCut N b A <;> simp only [hd, if_true, if_false] <;> ring

/-- A finite-coordinate algebra lemma. Its premise is instantiated below by
the derived actual source identity, not a desired source-law assumption. -/
lemma directedExposure_difference_of_coordinate (w w' : CladeWeights X)
    (D : Finset X) (δ : ℝ)
    (hw : ∀ B, (w B : ℝ) - (w' B : ℝ) = if B = D then δ else 0) (i j : X) :
    directedExposure w i j - directedExposure w' i j =
      if i ∈ D ∧ j ∉ D then δ else 0 := by
  unfold directedExposure
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ B : Finset X, if B = D then (if i ∈ D ∧ j ∉ D then δ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro B _
      by_cases hB : B = D
      · subst B
        by_cases hij : i ∈ D ∧ j ∉ D <;> simp [hij, hw D]
      · by_cases hij : i ∈ B ∧ j ∉ B <;> simp [hij, hw B, hB]
    _ = _ := by simp

/-- The actual directed exposure changes by the chosen-arm exposure difference
exactly for inside-to-outside pairs of the fixed original child bridge cut. -/
theorem directedExposure_bank_difference (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (hc : CutChild N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E) (coin coin' : CommonSeed N)
    (hcoin : ∀ h, h ≠ removedHybrid N b A → coin h = coin' h) (i j : X) :
    directedExposure (weightedNormalize N C H r coin) i j -
      directedExposure (weightedNormalize N C H r coin') i j =
        if i ∈ childCut N b A ∧ j ∉ childCut N b A then
          exposure N C r (chosenArm N H b A coin) -
            exposure N C r (chosenArm N H b A coin') else 0 := by
  exact directedExposure_difference_of_coordinate _ _ _ _
    (weightedNormalize_bank_difference N C H hc b hb A r coin coin' hcoin) i j

/-- The same difference for the existing original-edge selected-path sum.
The previously selected grouping theorem supplies this final correspondence. -/
theorem selectedDirectedExposure_bank_difference
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (hc : CutChild N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (r : PositivePairRates E) (coin coin' : CommonSeed N)
    (hcoin : ∀ h, h ≠ removedHybrid N b A → coin h = coin' h) (i j : X) :
    DotG4.ActualSelectedPathExposure.selectedDirectedExposure N C H r coin i j -
      DotG4.ActualSelectedPathExposure.selectedDirectedExposure N C H r coin' i j =
        if i ∈ childCut N b A ∧ j ∉ childCut N b A then
          exposure N C r (chosenArm N H b A coin) -
            exposure N C r (chosenArm N H b A coin') else 0 := by
  rw [← weightedNormalize_directedExposure N C H r coin i j,
    ← weightedNormalize_directedExposure N C H r coin' i j]
  exact directedExposure_bank_difference N C H hc b hb A r coin coin' hcoin i j

#print axioms weightedNormalize_affine
#print axioms weightedNormalize_bank_difference
#print axioms directedExposure_bank_difference
#print axioms selectedDirectedExposure_bank_difference

end Astra.PhysicalSpliceAffine
