import Astra.PhysicalSpliceRates
import Astra.PhysicalSpliceClades
import G4WeightedOrdinaryTreeLaw

/-! Work in progress, uncompiled and unselected. These algebraic bridges use
the actual constructed rates; no weighted-tree or forest-law equality is an
input. Compilation and the actual type/axiom audit remain pending. -/
namespace Astra.PhysicalSpliceWeights

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open GProgram.G5.AttainedChronology
open G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph G1SplicedSourceAdmission
open GProgram.G7.OriginalSurvivalCoverage
open DotG4.WeightedOrdinaryTreeLaw Astra.PhysicalSpliceRates
open Astra.PhysicalSpliceRegistry Astra.PhysicalSpliceClades
open scoped Classical BigOperators

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]

lemma retained_edgeExposure (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : RetainedEdge N b A) :
    edgeExposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRates N C r b A) (.inl e) = edgeExposure N C r e.val := by
  apply NNReal.coe_injective
  exact retained_exposure N hc b hb A C r e

lemma new_edgeExposure (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (C : Calendar N.graph) (r : PositivePairRates E) :
    edgeExposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRates N C r b A) (.inr ()) =
      edgeExposure N C r A.entry + edgeExposure N C r A.fragment.parents.parent0 +
        edgeExposure N C r A.child := by
  apply NNReal.coe_injective
  exact new_edge_exposure N hc b hb A C r

lemma equal_arm_edgeExposure (N : RootedBinary V E X)
    (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (heq : exposure N C r A.fragment.parents.parent0 =
      exposure N C r A.fragment.parents.parent1) :
    edgeExposure N C r A.fragment.parents.parent0 =
      edgeExposure N C r A.fragment.parents.parent1 := by
  apply NNReal.coe_injective
  exact heq

/-- Pure finite bookkeeping of the exact four removed occurrences. This does
not replace their values by a stochastic or weighted-law hypothesis. -/
lemma sum_retained_and_four_removed (N : RootedBinary V E X)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (f : E → ℝ≥0) :
    (∑ e : E, f e) =
      (∑ e : RetainedEdge N b A, f e.val) + f A.entry + f A.child +
        f A.fragment.parents.parent0 + f A.fragment.parents.parent1 := by
  have hret : (∑ e ∈ (removedEdges N b A)ᶜ, f e) =
      ∑ e : RetainedEdge N b A, f e.val :=
    Finset.sum_subtype _ (fun _ => by simp only [Finset.mem_compl]) f
  have hsum := Finset.sum_compl_add_sum (removedEdges N b A) f
  rw [hret] at hsum
  simpa [removedEdges, actual_entry_child_distinct N b A,
    actual_entry_parent0_distinct N b A, actual_entry_parent1_distinct N b A,
    actual_child_parent0_distinct N b A, actual_child_parent1_distinct N b A,
    A.fragment.parents.different, add_assoc] using hsum.symm

lemma exactly_one_arm_kept (N : RootedBinary V E X)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (S : N.Switching) :
    (S.keep A.fragment.parents.parent0 ∧ ¬ S.keep A.fragment.parents.parent1) ∨
      (S.keep A.fragment.parents.parent1 ∧ ¬ S.keep A.fragment.parents.parent0) := by
  obtain ⟨e, ht, hk, hu⟩ :=
    S.hybrid_unique A.fragment.parents.hybrid A.fragment.parents.isHybrid
  rcases actual_hybrid_parents_exhaustive N b A e ht with rfl | rfl
  · exact Or.inl ⟨hk, fun h1 => A.fragment.parents.different
      (hu A.fragment.parents.parent1 A.fragment.parents.target1 h1).symm⟩
  · exact Or.inr ⟨hk, fun h0 => A.fragment.parents.different
      (hu A.fragment.parents.parent0 A.fragment.parents.target0 h0)⟩

/-- Every original bank has exactly the same normalized clade weights after
the constructed scalar splice. Equal exposure is used only to replace the
selected arm's scalar; no target profile or law equality is supplied. -/
theorem weightedNormalize_splice (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (r : PositivePairRates E)
    (heq : exposure N C r A.fragment.parents.parent0 =
      exposure N C r A.fragment.parents.parent1) (coin : CommonSeed N) :
    weightedNormalize (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRegistry N hc b hb A H) (splicedRates N C r b A)
        (restrictBank N hc b hb A coin) = weightedNormalize N C H r coin := by
  funext D
  by_cases hD : D = ∅ ∨ D = Finset.univ
  · simp only [weightedNormalize, if_pos hD]
  · have hDE : D ≠ ∅ := fun h => hD (Or.inl h)
    have hED : (∅ : Finset X) ≠ D := Ne.symm hDE
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
    have hentry := entry_edgeTaxa_eq_child N C H hc b A coin
    have hnew : newf (.inr ()) = oldf A.entry + oldf A.child +
        oldf A.fragment.parents.parent0 + oldf A.fragment.parents.parent1 := by
      rcases exactly_one_arm_kept N b A (commonSwitching N H coin) with
        ⟨hk0, hn1⟩ | ⟨hk1, hn0⟩
      · have hp : edgeTaxa N C H coin A.fragment.parents.parent0 =
            edgeTaxa N C H coin A.child :=
          kept_parent_edgeTaxa_eq_child N C H b A coin false hk0
        have hnone := edgeTaxa_empty_of_not_kept N C H coin
          A.fragment.parents.parent1 hn1
        dsimp only [newf, oldf]
        rw [new_edgeTaxa N C H hc b hb A coin,
          new_edgeExposure N hc b hb A C r, hentry, hp, hnone]
        by_cases hd : edgeTaxa N C H coin A.child = D
        · simp only [hd, if_true, if_neg hED, add_zero, zero_add] <;> ac_rfl
        · simp only [hd, if_false, if_neg hED, add_zero, zero_add]
      · have hp : edgeTaxa N C H coin A.fragment.parents.parent1 =
            edgeTaxa N C H coin A.child :=
          kept_parent_edgeTaxa_eq_child N C H b A coin true hk1
        have hnone := edgeTaxa_empty_of_not_kept N C H coin
          A.fragment.parents.parent0 hn0
        have he := equal_arm_edgeExposure N b A C r heq
        dsimp only [newf, oldf]
        rw [new_edgeTaxa N C H hc b hb A coin,
          new_edgeExposure N hc b hb A C r, hentry, hp, hnone]
        by_cases hd : edgeTaxa N C H coin A.child = D
        · simp only [hd, if_true, if_neg hED, add_zero, zero_add, he] <;> ac_rfl
        · simp only [hd, if_false, if_neg hED, add_zero, zero_add]
    simp only [weightedNormalize, if_neg hD]
    change (∑ e : SplicedEdge N b A, newf e) = ∑ e : E, oldf e
    calc
      (∑ e : SplicedEdge N b A, newf e) =
          (∑ e : RetainedEdge N b A, newf (.inl e)) + newf (.inr ()) := by
        simp only [Fintype.sum_sum_type, Fintype.sum_unique]
      _ = (∑ e : RetainedEdge N b A, oldf e.val) +
          (oldf A.entry + oldf A.child + oldf A.fragment.parents.parent0 +
            oldf A.fragment.parents.parent1) := by rw [hret, hnew]
      _ = ∑ e : E, oldf e := by
        simpa only [add_assoc] using (sum_retained_and_four_removed N b A oldf).symm

-- Unexecuted audit requests, not actual type or axiom output.
#check weightedNormalize_splice
#print axioms retained_edgeExposure
#print axioms new_edgeExposure
#print axioms equal_arm_edgeExposure
#print axioms sum_retained_and_four_removed
#print axioms exactly_one_arm_kept
#print axioms weightedNormalize_splice

end Astra.PhysicalSpliceWeights
