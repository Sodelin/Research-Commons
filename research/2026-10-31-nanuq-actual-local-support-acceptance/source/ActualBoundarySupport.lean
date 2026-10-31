import ActualBoundaryCut

/-! UNCOMPILED exact adjacent-boundary quartet ↔ EXISTING whole displayed
split. This is not a definition of display via quartet support. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.ActualFinite Nanuq.AdjacentCertificate
open GProgram.G5.Normalization G1ActualDisplayedClusterSplitTransport
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

def rankIntervalSide {n : Nat} (rank : X ≃ Fin n) (i j : Nat) : Finset X :=
  Finset.univ.filter (fun x => i<(rank x).val ∧ (rank x).val≤j)

@[simp] theorem mem_rankIntervalSide {n : Nat} (rank : X ≃ Fin n) (i j : Nat) (x : X) :
    x∈rankIntervalSide rank i j ↔ i<(rank x).val ∧ (rank x).val≤j := by
  simp [rankIntervalSide]

theorem actual_boundary_split_iff (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (hsets : ∀ q : Fin 4 ↪ X,
      N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
        ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩)
    (i j : Nat) (hij : i<j) (hjn : j<n)
    (q : Fin 4 ↪ X)
    (h0 : (rank (q 0)).val=i+1) (h1 : (rank (q 1)).val=j)
    (h2 : (rank (q 2)).val=i)
    (h3 : (rank (q 3)).val=if j+1=n then 0 else j+1) :
    Resolution.xy_zw ∈ N.rawDisplayedQuartets q ↔
      ({rankIntervalSide rank i j, Finset.univ \ rankIntervalSide rank i j} :
        Finset (Finset X)) ∈ actualDisplayedSplits N Finset.univ := by
  let B := rankIntervalSide rank i j
  have hb0 : q 0∈B := by simp only [B,mem_rankIntervalSide,h0]; omega
  have hb1 : q 1∈B := by simp only [B,mem_rankIntervalSide,h1]; omega
  have hb2 : q 2∉B := by simp only [B,mem_rankIntervalSide,h2]; omega
  have hb3 : q 3∉B := by
    simp only [B,mem_rankIntervalSide,h3]
    split_ifs <;> omega
  constructor
  · intro hq
    obtain ⟨S,e,hor⟩ := actual_boundary_resolution_whole_cut N n mask rank T hs hsets
      i j hij hjn q h0 h1 h2 h3 hq
    apply actual_split_of_edge_side N S e B ⟨q 0,hb0⟩
      ⟨q 2,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hb2⟩⟩
    simpa only [B,mem_rankIntervalSide] using hor
  · intro hsplit
    obtain ⟨S,e,hn,hp,he⟩ := (actual_displayed_split_edge_iff N Finset.univ _).mp hsplit
    let D := sampledDescendants N S Finset.univ (S.graph.target e)
    have hBm : B∈({D,Finset.univ \ D} : Finset (Finset X)) := by
      rw [←he]
      simp [B]
    have hBD : B=D ∨ B=Finset.univ \ D := by simpa using hBm
    have hd (x : X) : x∈D ↔ S.graph.DReach (S.graph.target e) (N.leaf x) := by
      simp [D,sampledDescendants]
    apply (actual_first_pair_cut_iff N q).mpr
    refine ⟨S,e,?_⟩
    rcases hBD with hBD | hBD
    · rw [hBD] at hb0 hb1 hb2 hb3
      exact Or.inl ⟨(hd _).mp hb0,(hd _).mp hb1,
        fun h => hb2 ((hd _).mpr h),fun h => hb3 ((hd _).mpr h)⟩
    · rw [hBD] at hb0 hb1 hb2 hb3
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] at hb0 hb1 hb2 hb3
      exact Or.inr ⟨fun h => hb0 ((hd _).mpr h),fun h => hb1 ((hd _).mpr h),
        (hd _).mp hb2,(hd _).mp hb3⟩

end Nanuq.ActualCutClusters
