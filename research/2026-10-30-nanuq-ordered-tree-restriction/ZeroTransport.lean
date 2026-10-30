import CoefficientTransport
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

theorem displayedPair_transport (n : Nat) (keep : Nat → Bool) (T U : Tree) (tips tips' : List Nat)
    (ht : EdgeTransport n keep T U tips tips') (x y p z : Nat)
    (hx : x∈retained n keep) (hy : y∈retained n keep) (hp : p∈retained n keep) (hz : z∈retained n keep)
    (hxy : x≠y) (hxp : x≠p) (hxz : x≠z) (hyp : y≠p) (hyz : y≠z) (hpz : p≠z) :
    displayedPair (quartets n) (codedPattern T tips n) x y p z =
      displayedPair (quartets (retained n keep).length) (codedPattern U tips' (retained n keep).length)
        ((retained n keep).idxOf x) ((retained n keep).idxOf y)
        ((retained n keep).idxOf p) ((retained n keep).idxOf z) := by
  have hq := query_transport n keep T U tips tips' ht x y p z hx hy hp hz hxy hxp hxz hyp hyz hpz
  simp only [displayedPair,hq.1,hq.2,relabel_side_rank,hx,hy]

theorem boundary_query_distinct (n i j : Nat) (hn : 3≤n) (hi : i<n) (hj : j<n) (hij : i<j)
    (nonadj : i+1<j ∧ ¬(i=0 ∧ j+1=n)) :
    (i+1)%n≠j ∧ (i+1)%n≠i ∧ (i+1)%n≠(j+1)%n ∧ j≠i ∧ j≠(j+1)%n ∧ i≠(j+1)%n := by
  have hbi : i+1<n := by omega
  rw [Nat.mod_eq_of_lt hbi]
  by_cases hd : j+1<n
  · rw [Nat.mod_eq_of_lt hd]; omega
  · have he : j+1=n := by omega
    rw [he,Nat.mod_self]; omega

 theorem retained_nonadjacent (n : Nat) (keep : Nat → Bool) (i j : Nat)
    (hn : 3≤n) (hi : i<n) (hj : j<n) (hij : i<j)
    (nonadj : i+1<j ∧ ¬(i=0 ∧ j+1=n))
    (hA : i∈retained n keep) (hB : (i+1)%n∈retained n keep)
    (hC : j∈retained n keep) (hD : (j+1)%n∈retained n keep) :
    (retained n keep).idxOf i+1 < (retained n keep).idxOf j ∧
      ¬((retained n keep).idxOf i=0 ∧ (retained n keep).idxOf j+1=(retained n keep).length) := by
  have ho := retained_rank_strict n keep i j hA hC hij
  have hjb := List.idxOf_lt_length_iff.mpr hC
  have hi1 : i+1<n := by omega
  have hbLt : (i+1)%n<j := by rw [Nat.mod_eq_of_lt hi1]; exact nonadj.1
  have hob := retained_rank_strict n keep ((i+1)%n) j hB hC hbLt
  have hbg := retained_gap_next n keep i ((i+1)%n) (range_gap n i (by omega) hi)
    (List.mem_filter.mp hA).2 (List.mem_filter.mp hB).2
  have hdg := retained_gap_next n keep j ((j+1)%n) (range_gap n j (by omega) hj)
    (List.mem_filter.mp hC).2 (List.mem_filter.mp hD).2
  have hsmall : (retained n keep).idxOf i+1 < (retained n keep).length := by omega
  rw [Nat.mod_eq_of_lt hsmall] at hbg
  refine ⟨by omega,?_⟩
  rintro ⟨hzero,hlast⟩
  rw [hlast,Nat.mod_self] at hdg
  have heq : (retained n keep).idxOf i=(retained n keep).idxOf ((j+1)%n) := hzero.trans hdg.symm
  have hne := (boundary_query_distinct n i j hn hi hj hij nonadj).2.2.2.2.2
  exact hne ((List.idxOf_inj hA).mp heq)

theorem all_size_absent_boundary_zero (n mask : Nat) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (p q i j : Nat) (hp : p<n) (hq : q<n) (hi : i<n) (hj : j<n) (hpq : p<q) (hij : i<j)
    (nonadj : i+1<j ∧ ¬(i=0 ∧ j+1=n))
    (absent : displayedPair (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      ((i+1)%n) j i ((j+1)%n)=false) :
    alpha n (quartets n) (codedPattern T (occurrenceLabels n mask) n) p q i j=0 := by
  let keep := queryKeep i ((i+1)%n) j ((j+1)%n) p q
  have hcount : 3≤(retained n keep).length ∧ (retained n keep).length≤6 :=
    ⟨retained_boundary_ge_three n i j p q hn hi hj hij,
      retained_query_le_six n i ((i+1)%n) j ((j+1)%n) p q⟩
  obtain ⟨newMask,U,hbound,hsize,hcheck,ht⟩ := construct_transport n mask keep T (by omega) hs hcount
  have hn0 : 0<n := by omega
  have hA : i∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hi (by simp)
  have hB : (i+1)%n∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ (Nat.mod_lt _ hn0) (by simp)
  have hC : j∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hj (by simp)
  have hD : (j+1)%n∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ (Nat.mod_lt _ hn0) (by simp)
  have hP : p∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hp (by simp)
  have hQ : q∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hq (by simp)
  have hd := boundary_query_distinct n i j hn hi hj hij nonadj
  have hdisp := displayedPair_transport n keep T U (occurrenceLabels n mask)
    (occurrenceLabels (retained n keep).length newMask) ht ((i+1)%n) j i ((j+1)%n)
    hB hC hA hD hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2
  have hbg := retained_gap_next n keep i ((i+1)%n) (range_gap n i (by omega) hi)
    (List.mem_filter.mp hA).2 (List.mem_filter.mp hB).2
  have hdg := retained_gap_next n keep j ((j+1)%n) (range_gap n j (by omega) hj)
    (List.mem_filter.mp hC).2 (List.mem_filter.mp hD).2
  have hnewabs : displayedPair (quartets (retained n keep).length)
      (codedPattern U (occurrenceLabels (retained n keep).length newMask) (retained n keep).length)
      (((retained n keep).idxOf i+1)%(retained n keep).length) ((retained n keep).idxOf j)
      ((retained n keep).idxOf i) (((retained n keep).idxOf j+1)%(retained n keep).length)=false := by
    rw [←hbg,←hdg,←hdisp]
    exact absent
  rw [coefficient_transport n keep T U (occurrenceLabels n mask)
    (occurrenceLabels (retained n keep).length newMask) ht p q i j (by omega) hi hj
    (by omega) hP hQ hA hB hC hD]
  exact absent_zero_of_check _ _ _ hcheck _ _ _ _
    (List.idxOf_lt_length_iff.mpr hP) (List.idxOf_lt_length_iff.mpr hQ)
    (List.idxOf_lt_length_iff.mpr hA) (List.idxOf_lt_length_iff.mpr hC)
    (retained_rank_strict n keep p q hP hQ hpq) (retained_rank_strict n keep i j hA hC hij)
    (retained_nonadjacent n keep i j hn hi hj hij nonadj hA hB hC hD) hnewabs

#print axioms retained_nonadjacent
#print axioms all_size_absent_boundary_zero
end Nanuq.Restriction
