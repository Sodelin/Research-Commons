import ActualBoundaryCoordinates

/-! UNCOMPILED completion of the source support direction: EVERY existing
actual displayed split is an interval in the SAME derived local rank.
This is not compatibility with an independently GIVEN global taxon order. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.ActualFinite Nanuq.AdjacentCertificate
open Nanuq.Weighted
open GProgram.G5.Normalization G1ActualDisplayedClusterSplitTransport
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

theorem actual_all_splits_are_rank_intervals (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (hsets : ∀ q : Fin 4 ↪ X,
      N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
        ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩)
    (cut : Finset (Finset X)) (hcut : cut∈actualDisplayedSplits N Finset.univ) :
    ∃ i j : Nat, i<j ∧ j<n ∧
      cut={rankIntervalSide rank i j,Finset.univ \ rankIntervalSide rank i j} := by
  obtain ⟨S,e,hn,hp,he⟩ := (actual_displayed_split_edge_iff N Finset.univ cut).mp hcut
  obtain ⟨i,j,hij,hjn,hor⟩ := actual_proper_cut_interval N n mask rank T hs hsets S e hn hp
  refine ⟨i,j,hij,hjn,?_⟩
  rcases hor with hor | hor
  · have hd : sampledDescendants N S Finset.univ (S.graph.target e)=rankIntervalSide rank i j := by
      ext x
      have hx := hor (rank x)
      simpa [sampledDescendants,mem_rankIntervalSide] using hx
    simpa [hd] using he
  · have hd : sampledDescendants N S Finset.univ (S.graph.target e)=
        Finset.univ \ rankIntervalSide rank i j := by
      ext x
      have hx := hor (rank x)
      simp only [rank.symm_apply_apply] at hx
      simp only [sampledDescendants,Finset.mem_filter,Finset.mem_univ,true_and,
        Finset.mem_sdiff,mem_rankIntervalSide,true_and]
      tauto
    have hcc : Finset.univ \ (Finset.univ \ rankIntervalSide rank i j)=rankIntervalSide rank i j := by
      ext x; simp
    rw [hd,hcc] at he
    rw [he]
    ext A
    simp [or_comm]

theorem adjacent_gap_cases {n : Nat} (i j : Fin n) (hij : i<j)
    (hadj : ¬(i.val+1<j.val ∧ ¬(i.val=0 ∧ j.val+1=n))) :
    j=cyclicNext i ∨ i=cyclicNext j := by
  by_cases hs : i.val+1=j.val
  · left
    apply Fin.ext
    change j.val=(i.val+1)%n
    rw [hs,Nat.mod_eq_of_lt j.isLt]
  · have he : i.val=0 ∧ j.val+1=n := by
      have hjn := j.isLt
      have hi : i.val<j.val := hij
      have hstrict : i.val+1<j.val := by omega
      by_contra h
      exact hadj ⟨hstrict,h⟩
    right
    apply Fin.ext
    change i.val=(j.val+1)%n
    simp [he.1,he.2]

theorem rank_value_eq_iff {n : Nat} (rank : X ≃ Fin n) (x : X) (a : Fin n) :
    (rank x).val=a.val ↔ x=rank.symm a := by
  constructor
  · intro h
    have he : rank x=a := Fin.ext h
    simpa using congrArg rank.symm he
  · rintro rfl
    simp

theorem actual_adjacent_split_mem (N : RootedBinary V E X)
    {n : Nat} (rank : X ≃ Fin n) (i j : Fin n) (hij : i<j)
    (hadj : ¬(i.val+1<j.val ∧ ¬(i.val=0 ∧ j.val+1=n))) :
    ({rankIntervalSide rank i.val j.val,Finset.univ \ rankIntervalSide rank i.val j.val} :
      Finset (Finset X)) ∈ actualDisplayedSplits N Finset.univ := by
  have hne : rank.symm i≠rank.symm j := fun h => (ne_of_lt hij) (rank.symm.injective h)
  by_cases hs : i.val+1=j.val
  · have hB : rankIntervalSide rank i.val j.val={rank.symm j} := by
      ext x
      rw [mem_rankIntervalSide,Finset.mem_singleton,←rank_value_eq_iff]
      omega
    have hp := actual_pendant_split_mem N Finset.univ (rank.symm j) (Finset.mem_univ _)
      ⟨rank.symm i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,by simpa using hne⟩⟩
    simpa [hB] using hp
  · have he : i.val=0 ∧ j.val+1=n := by
      have hi : i.val<j.val := hij
      have hstrict : i.val+1<j.val := by omega
      by_contra h
      exact hadj ⟨hstrict,h⟩
    have hBc : Finset.univ \ rankIntervalSide rank i.val j.val={rank.symm i} := by
      ext x
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,mem_rankIntervalSide,
        Finset.mem_singleton,←rank_value_eq_iff]
      have hx := (rank x).isLt
      omega
    have hB : rankIntervalSide rank i.val j.val=Finset.univ \ {rank.symm i} := by
      calc
        _ = Finset.univ \ (Finset.univ \ rankIntervalSide rank i.val j.val) := by ext x; simp
        _ = _ := by rw [hBc]
    have hp := actual_pendant_split_mem N Finset.univ (rank.symm i) (Finset.mem_univ _)
      ⟨rank.symm j,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,by simpa using Ne.symm hne⟩⟩
    rw [hBc,hB]
    have hpair : ({Finset.univ \ {rank.symm i},{rank.symm i}} : Finset (Finset X)) =
        {{rank.symm i},Finset.univ \ {rank.symm i}} := by ext A; simp [or_comm]
    rw [hpair]
    exact hp

end Nanuq.ActualCutClusters
