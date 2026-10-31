import ActualLocalSupport

/-! UNCOMPILED low-port algebra. The fixed tip/fork objects below are ONLY
zero-quartet algebraic receivers, NOT asserted source tree representations.
No four-label embedding exists, so all original anchor contributions are
literal overlap cases. Every original pendant split is proved separately. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.ActualFinite Nanuq.AdjacentCertificate
open Nanuq.Weighted Nanuq.Reconstruction
open G1ActualDisplayedClusterSplitTransport
open scoped Classical BigOperators
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

theorem no_four_port_embedding {n : Nat} (rank : X ≃ Fin n) (hn : n<4)
    (q : Fin 4 ↪ X) : False := by
  have h := Fintype.card_le_of_injective (q.trans rank.toEmbedding) (q.trans rank.toEmbedding).injective
  simp only [Fintype.card_fin] at h
  omega

theorem finiteWeightedMatrix_two_zero (mask : Nat) (T : Tree) (m : Fin 2 → ℚ)
    (x y : Fin 2) : finiteWeightedMatrix 2 mask T m x y=0 := by
  unfold finiteWeightedMatrix
  rw [←upperSum_eq_pair_sum]
  unfold upperSum
  fin_cases x <;> fin_cases y <;> simp [Fin.sum_univ_succ,anchor]

theorem actual_two_port_zero (N : RootedBinary V E X) (rank : X ≃ Fin 2)
    (m : X → ℚ) (x y : X) : N.actualWeightedAnchorDistance m x y=0 := by
  have hs : Tree.tip.size=(occurrenceLabels 2 0).length-1 := by decide +kernel
  have hm : ∀ q : Fin 4 ↪ X,
      N.rawQuartetMean q=distinctMean (finiteResolutionSet Tree.tip (occurrenceLabels 2 0)
        (coordinateQuartet (fun i => (rank (q i)).val))) := by
    intro q
    exact False.elim (no_four_port_embedding rank (by decide) q)
  have he := actual_weighted_anchor_ranked N 2 0 rank Tree.tip hs hm m (rank x) (rank y)
  rw [finiteWeightedMatrix_two_zero] at he
  simpa using he

theorem actual_three_port_support (N : RootedBinary V E X) (rank : X ≃ Fin 3)
    (m : X → ℚ) (hm : ∀ x, 0<m x) :
    CircularDecomposable (fun x y => N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y)) ∧
    (∀ i j : Fin 3, i<j →
      (0<circularAlpha (fun x y => N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y)) i j ↔
        ({rankIntervalSide rank i.val j.val,Finset.univ \ rankIntervalSide rank i.val j.val} :
          Finset (Finset X)) ∈ actualDisplayedSplits N Finset.univ)) ∧
    (∀ cut∈actualDisplayedSplits N Finset.univ, ∃ i j : Nat, i<j ∧ j<3 ∧
      cut={rankIntervalSide rank i j,Finset.univ \ rankIntervalSide rank i j}) := by
  let T := Tree.fork Tree.tip Tree.tip
  have hs : T.size=(occurrenceLabels 3 0).length-1 := by
    change (Tree.fork Tree.tip Tree.tip).size=(occurrenceLabels 3 0).length-1
    decide +kernel
  have hsets : ∀ q : Fin 4 ↪ X,
      N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels 3 0)
        ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩ := by
    intro q
    exact False.elim (no_four_port_embedding rank (by decide) q)
  have hmean : ∀ q : Fin 4 ↪ X,
      N.rawQuartetMean q=distinctMean (finiteResolutionSet T (occurrenceLabels 3 0)
        (coordinateQuartet (fun i => (rank (q i)).val))) := by
    intro q
    exact False.elim (no_four_port_embedding rank (by decide) q)
  exact actual_weighted_all_interval_support N 3 0 rank T (by decide) hs hsets hmean m hm

end Nanuq.ActualCutClusters
