import FiniteWeightedCoefficients
import NanuqActualWeightedAnchorComposition

/-! UNCOMPILED literal original anchor-sum identification. The diagonal is
zeroed BEFORE ordered/unordered conversion, so the finite equal-anchor
mismatch is never used. Rank is the SAME actual canonical receiver witness. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualFinite
open Nanuq.Source Nanuq.Quartet Nanuq.AdjacentCertificate Nanuq.Restriction
open Nanuq.Weighted
open scoped Classical BigOperators
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem sum_reindex_rank {Y : Type*} [Fintype Y] (n : Nat)
    (rank : Y ≃ Fin n) (f : Y → ℚ) :
    (∑ y, f y) = ∑ i, f (rank.symm i) := by
  apply Finset.sum_bij (fun y _ => rank y)
  · intro y _; exact Finset.mem_univ _
  · intro a _ b _ h; exact rank.injective h
  · intro i _; exact ⟨rank.symm i,Finset.mem_univ _,rank.apply_symm_apply i⟩
  · intro y _; rw [rank.symm_apply_apply]

theorem actual_ranked_anchor_entry (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (hm : ∀ q : Fin 4 ↪ X,
      N.rawQuartetMean q=distinctMean (finiteResolutionSet T (occurrenceLabels n mask)
        (coordinateQuartet (fun i => (rank (q i)).val))))
    (x y p q : Fin n) :
    N.actualTupleAnchor ![rank.symm x,rank.symm y,rank.symm p,rank.symm q] =
      if p=q then 0 else
        (anchor (quartets n) (codedPattern T (occurrenceLabels n mask) n)
          p.val q.val x.val y.val : ℚ) := by
  by_cases hpq : p=q
  · subst q
    simp only [ite_true]
    exact actual_diagonal_anchor N _ rfl
  · rw [if_neg hpq]
    have hne : rank.symm p≠rank.symm q := fun h => hpq (rank.symm.injective h)
    have h := actual_sorted_anchor N n mask rank T hs hm
      ![rank.symm x,rank.symm y,rank.symm p,rank.symm q] hne
    simpa using h.symm

theorem actual_weighted_anchor_ranked (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (hm : ∀ q : Fin 4 ↪ X,
      N.rawQuartetMean q=distinctMean (finiteResolutionSet T (occurrenceLabels n mask)
        (coordinateQuartet (fun i => (rank (q i)).val))))
    (m : X → ℚ) (x y : Fin n) :
    N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y) =
      finiteWeightedMatrix n mask T (fun p => m (rank.symm p)) x y := by
  unfold RootedBinary.actualWeightedAnchorDistance
  rw [sum_reindex_rank n rank]
  simp_rw [sum_reindex_rank n rank]
  simp_rw [actual_ranked_anchor_entry N n mask rank T hs hm]
  let f : Fin n → Fin n → ℚ := fun p q => m (rank.symm p)*m (rank.symm q)*
    (if p=q then 0 else (anchor (quartets n)
      (codedPattern T (occurrenceLabels n mask) n) p.val q.val x.val y.val : ℚ))
  have hsym : ∀ p q, f p q=f q p := by
    intro p q
    by_cases he : p=q
    · subst q; rfl
    · simp only [f,if_neg he,if_neg (Ne.symm he),
        anchor_anchor_swap (quartets n) (codedPattern T (occurrenceLabels n mask) n)
          p.val q.val x.val y.val]
      ring
  have hdiag : ∀ p, f p p=0 := by intro p; simp [f]
  change (∑ p,∑ q,f p q)/2= _
  rw [ordered_pair_sum_eq_twice_upperPairs f hsym hdiag]
  have hscale : (2 * ∑ pq ∈ upperPairs n, f pq.1 pq.2) / 2 =
      ∑ pq ∈ upperPairs n, f pq.1 pq.2 := by ring
  rw [hscale]
  unfold finiteWeightedMatrix
  apply Finset.sum_congr rfl
  intro pq hpq
  have he : pq.1≠pq.2 := ne_of_lt ((mem_upperPairs _ _).mp hpq)
  simp [f,he]

end Nanuq.ActualFinite
