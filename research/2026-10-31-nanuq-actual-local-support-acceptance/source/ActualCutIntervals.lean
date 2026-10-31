import RankedCutInterval

/-! UNCOMPILED derivation of interval support for every proper original
switching cut in the SAME canonical rank. No circularity premise. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.ActualFinite Nanuq.AdjacentCertificate
open GProgram.G5.Normalization
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem rank_image_mem (n : Nat) (rank : X ≃ Fin n) (D : Finset X) (a : Fin n) :
    a.val ∈ D.image (fun x => (rank x).val) ↔ rank.symm a ∈ D := by
  constructor
  · intro ha
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp ha
    have hr : rank x=a := Fin.ext he
    have hx' : x=rank.symm a := by rw [←hr,rank.symm_apply_apply]
    exact hx' ▸ hx
  · intro hx
    exact Finset.mem_image.mpr ⟨rank.symm a,hx,by simp⟩

theorem actual_proper_cut_interval (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (hsets : ∀ q : Fin 4 ↪ X,
      N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
        ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩)
    (S : N.Switching) (e : S.Edge)
    (hne : (sampledDescendants N S Finset.univ (S.graph.target e)).Nonempty)
    (hproper : (Finset.univ \ sampledDescendants N S Finset.univ (S.graph.target e)).Nonempty) :
    ∃ i j : Nat, i<j ∧ j<n ∧
      ((∀ a : Fin n, S.graph.DReach (S.graph.target e) (N.leaf (rank.symm a)) ↔
          i<a.val ∧ a.val≤j) ∨
       (∀ a : Fin n, ¬S.graph.DReach (S.graph.target e) (N.leaf (rank.symm a)) ↔
          i<a.val ∧ a.val≤j)) := by
  let D := sampledDescendants N S Finset.univ (S.graph.target e)
  let B := D.image (fun x => (rank x).val)
  have hB (a : Fin n) : a.val∈B ↔
      S.graph.DReach (S.graph.target e) (N.leaf (rank.symm a)) := by
    rw [rank_image_mem]
    simp [D,sampledDescendants]
  have hbound : ∀ x∈B, x<n := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (rank y).isLt
  have hBn : B.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨(rank x).val,Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩
  have hCn : (Finset.range n \ B).Nonempty := by
    obtain ⟨x,hx⟩ := hproper
    have hnot : x∉D := (Finset.mem_sdiff.mp hx).2
    refine ⟨(rank x).val,Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (rank x).isLt,?_⟩⟩
    intro hxB
    have hd := (rank_image_mem n rank D (rank x)).mp hxB
    exact hnot (by simpa using hd)
  obtain ⟨A,hAn,hAz,hAb,hor⟩ : ∃ A : Finset Nat, A.Nonempty ∧ 0∉A ∧
      (∀ x∈A,x<n) ∧ (A=B ∨ A=Finset.range n \ B) := by
    by_cases hz : 0∈B
    · refine ⟨Finset.range n \ B,hCn,?_,?_,Or.inr rfl⟩
      · exact fun h => (Finset.mem_sdiff.mp h).2 hz
      · intro x hx; exact Finset.mem_range.mp (Finset.mem_sdiff.mp hx).1
    · exact ⟨B,hBn,hz,hbound,Or.inl rfl⟩
  have hAo : (∀ a : Fin n, a.val∈A ↔
      S.graph.DReach (S.graph.target e) (N.leaf (rank.symm a))) ∨
      (∀ a : Fin n, a.val∈A ↔
      ¬S.graph.DReach (S.graph.target e) (N.leaf (rank.symm a))) := by
    rcases hor with hor | hor
    · exact Or.inl (by intro a; rw [hor]; exact hB a)
    · exact Or.inr (by intro a; simp [hor,Finset.mem_range.mpr a.isLt,hB a])
  have hc := actual_ranked_cut_no_hole N n mask rank T hs hsets S e A hAb hAz hAo
  obtain ⟨i,j,hij,hA⟩ := convex_side_interval A hAn hAz hc
  have hj : j∈A := by rw [hA]; exact Finset.mem_Ioc.mpr ⟨hij,le_rfl⟩
  refine ⟨i,j,hij,hAb j hj,?_⟩
  rcases hAo with h | h
  · exact Or.inl (by intro a; rw [←h a,hA,Finset.mem_Ioc])
  · exact Or.inr (by intro a; rw [←h a,hA,Finset.mem_Ioc])

end Nanuq.ActualCutClusters
