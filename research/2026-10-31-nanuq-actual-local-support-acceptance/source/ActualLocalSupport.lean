import ActualCircularSupport

/-! UNCOMPILED exact local-support receiver. Its finite source equalities
are discharged by the actual cap receiver (or explicit ≤3-label vacuity),
not supplied as new original-network assumptions. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.ActualFinite Nanuq.AdjacentCertificate
open Nanuq.Weighted Nanuq.Reconstruction
open G1ActualDisplayedClusterSplitTransport
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

theorem actual_weighted_all_interval_support (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (hsets : ∀ q : Fin 4 ↪ X,
      N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
        ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩)
    (hmean : ∀ q : Fin 4 ↪ X,
      N.rawQuartetMean q=distinctMean (finiteResolutionSet T (occurrenceLabels n mask)
        (coordinateQuartet (fun i => (rank (q i)).val))))
    (m : X → ℚ) (hm : ∀ x, 0<m x) :
    CircularDecomposable (fun x y => N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y)) ∧
    (∀ i j : Fin n, i<j →
      (0<circularAlpha (fun x y => N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y)) i j ↔
        ({rankIntervalSide rank i.val j.val,Finset.univ \ rankIntervalSide rank i.val j.val} :
          Finset (Finset X)) ∈ actualDisplayedSplits N Finset.univ)) ∧
    (∀ cut∈actualDisplayedSplits N Finset.univ, ∃ i j : Nat, i<j ∧ j<n ∧
      cut={rankIntervalSide rank i j,Finset.univ \ rankIntervalSide rank i j}) := by
  have he : (fun x y => N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y)) =
      finiteWeightedMatrix n mask T (fun p => m (rank.symm p)) := by
    funext x y
    exact actual_weighted_anchor_ranked N n mask rank T hs hmean m x y
  refine ⟨?_,?_,?_⟩
  · rw [he]
    exact finiteWeightedMatrix_circular n mask T hn hs _ (fun p => le_of_lt (hm _))
  · intro i j hij
    by_cases hnon : i.val+1<j.val ∧ ¬(i.val=0 ∧ j.val+1=n)
    · exact actual_weighted_nontrivial_split_support N n mask rank T hn hs hsets hmean m hm i j hij hnon
    · have hsplit := actual_adjacent_split_mem N rank i j hij hnon
      have hpos : 0<circularAlpha (fun x y =>
          N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y)) i j := by
        rw [he]
        exact finiteWeightedMatrix_pendant_positive n mask T hn hs _ (fun p => hm _)
          i j hij (adjacent_gap_cases i j hij hnon)
      exact ⟨fun _ => hsplit,fun _ => hpos⟩
  · intro cut hc
    exact actual_all_splits_are_rank_intervals N n mask rank T hs hsets cut hc

end Nanuq.ActualCutClusters
