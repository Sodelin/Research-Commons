import ActualBoundarySupport
import ActualDisplayedPair
import ActualWeightedRanked

/-! UNCOMPILED exact adjacent tuple construction and original weighted
coefficient support. All inputs are derived by ONE actual receiver upstream. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.ActualFinite Nanuq.AdjacentCertificate
open Nanuq.Restriction Nanuq.Weighted
open G1ActualDisplayedClusterSplitTransport
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

def boundaryTuple {n : Nat} (i j : Fin n) : Fin 4 → Fin n :=
  ![cyclicNext i,j,i,cyclicNext j]

theorem boundaryTuple_injective {n : Nat} (hn : 3≤n) (i j : Fin n) (hij : i<j)
    (nonadj : i.val+1<j.val ∧ ¬(i.val=0 ∧ j.val+1=n)) :
    Function.Injective (boundaryTuple i j) := by
  have hd := boundary_query_distinct n i.val j.val hn i.isLt j.isLt hij nonadj
  obtain ⟨h01,h02,h03,h12,h13,h23⟩ := hd
  intro a b hab
  have he := congrArg Fin.val hab
  fin_cases a <;> fin_cases b <;> simp [boundaryTuple,cyclicNext] at he ⊢ <;> omega

theorem actual_boundary_displayedPair_iff (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (hsets : ∀ q : Fin 4 ↪ X,
      N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
        ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩)
    (hm : ∀ q : Fin 4 ↪ X,
      N.rawQuartetMean q=distinctMean (finiteResolutionSet T (occurrenceLabels n mask)
        (coordinateQuartet (fun i => (rank (q i)).val))))
    (i j : Fin n) (hij : i<j)
    (nonadj : i.val+1<j.val ∧ ¬(i.val=0 ∧ j.val+1=n)) :
    displayedPair (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      ((i.val+1)%n) j.val i.val ((j.val+1)%n)=true ↔
      ({rankIntervalSide rank i.val j.val,Finset.univ \ rankIntervalSide rank i.val j.val} :
        Finset (Finset X)) ∈ actualDisplayedSplits N Finset.univ := by
  let q : Fin 4 ↪ X := ⟨fun a => rank.symm (boundaryTuple i j a),
    fun a b h => boundaryTuple_injective hn i j hij nonadj (rank.symm.injective h)⟩
  have hr (a : Fin 4) : rank (q a)=boundaryTuple i j a := rank.apply_symm_apply _
  have hpair := actual_displayedPair_iff N n mask rank T hs hm q
  simp only [hr,boundaryTuple,cyclicNext] at hpair
  rw [hpair]
  apply actual_boundary_split_iff N n mask rank T hs hsets i.val j.val hij j.isLt q
  · have hjn := j.isLt
    simp [hr,boundaryTuple,cyclicNext,Nat.mod_eq_of_lt (show i.val+1<n by omega)]
  · simp [hr,boundaryTuple]
  · simp [hr,boundaryTuple]
  · have hjn := j.isLt
    simp [hr,boundaryTuple,cyclicNext]
    by_cases he : j.val+1=n
    · simp [he]
    · simp [he,Nat.mod_eq_of_lt (show j.val+1<n by omega)]

theorem actual_weighted_nontrivial_split_support (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (hsets : ∀ q : Fin 4 ↪ X,
      N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
        ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩)
    (hmean : ∀ q : Fin 4 ↪ X,
      N.rawQuartetMean q=distinctMean (finiteResolutionSet T (occurrenceLabels n mask)
        (coordinateQuartet (fun i => (rank (q i)).val))))
    (m : X → ℚ) (hm : ∀ x, 0<m x) (i j : Fin n) (hij : i<j)
    (nonadj : i.val+1<j.val ∧ ¬(i.val=0 ∧ j.val+1=n)) :
    0<circularAlpha (fun x y => N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y)) i j ↔
      ({rankIntervalSide rank i.val j.val,Finset.univ \ rankIntervalSide rank i.val j.val} :
        Finset (Finset X)) ∈ actualDisplayedSplits N Finset.univ := by
  have he : (fun x y => N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y)) =
      finiteWeightedMatrix n mask T (fun p => m (rank.symm p)) := by
    funext x y
    exact actual_weighted_anchor_ranked N n mask rank T hs hmean m x y
  rw [he,finiteWeightedMatrix_nontrivial_support n mask T hn hs
    (fun p => m (rank.symm p)) (fun p => hm (rank.symm p)) i j hij nonadj]
  exact actual_boundary_displayedPair_iff N n mask rank T hn hs hsets hmean i j hij nonadj

end Nanuq.ActualCutClusters
