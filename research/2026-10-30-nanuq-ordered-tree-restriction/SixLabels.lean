import FiniteRestriction
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

def queryKeep (a b c d p q : Nat) (x : Nat) : Bool := [a,b,c,d,p,q].contains x

theorem retained_query_le_six (n a b c d p q : Nat) :
    (retained n (queryKeep a b c d p q)).length ≤ 6 := by
  have hn : (retained n (queryKeep a b c d p q)).Nodup :=
    (List.nodup_range (n:=n)).filter _
  have hs : retained n (queryKeep a b c d p q) ⊆ [a,b,c,d,p,q] := by
    intro x hx
    have h := (List.mem_filter.mp hx).2
    simpa only [queryKeep,List.contains_iff_mem] using h
  exact hn.length_le_of_subset hs

theorem next_ne (n i : Nat) (hn : 2≤n) (hi : i<n) : (i+1)%n ≠ i := by
  by_cases h : i+1<n
  · rw [Nat.mod_eq_of_lt h]; omega
  · have he : i+1=n := by omega
    rw [he,Nat.mod_self]; omega

theorem next_next_ne (n i : Nat) (hn : 3≤n) (hi : i<n) : (((i+1)%n)+1)%n ≠ i := by
  by_cases h : i+1<n
  · rw [Nat.mod_eq_of_lt h]
    by_cases h2 : i+1+1<n
    · rw [Nat.mod_eq_of_lt h2]; omega
    · have he : i+1+1=n := by omega
      rw [he,Nat.mod_self]; omega
  · have he : i+1=n := by omega
    rw [he,Nat.mod_self]
    have h1 : 0+1<n := by omega
    rw [Nat.mod_eq_of_lt h1]; omega

theorem retained_query_mem (n a b c d p q x : Nat) (hx : x<n)
    (hq : x∈[a,b,c,d,p,q]) : x∈retained n (queryKeep a b c d p q) := by
  exact List.mem_filter.mpr ⟨List.mem_range.mpr hx,by simpa only [queryKeep,List.contains_iff_mem] using hq⟩

theorem retained_boundary_ge_three (n i j p q : Nat) (hn : 3≤n) (hi : i<n) (hj : j<n) (hij : i<j) :
    3 ≤ (retained n (queryKeep i ((i+1)%n) j ((j+1)%n) p q)).length := by
  let P := retained n (queryKeep i ((i+1)%n) j ((j+1)%n) p q)
  have hn0 : 0<n := by omega
  have hA : i∈P := retained_query_mem _ _ _ _ _ _ _ _ hi (by simp)
  have hB : (i+1)%n∈P := retained_query_mem _ _ _ _ _ _ _ _ (Nat.mod_lt _ hn0) (by simp)
  have hC : j∈P := retained_query_mem _ _ _ _ _ _ _ _ hj (by simp)
  have hD : (j+1)%n∈P := retained_query_mem _ _ _ _ _ _ _ _ (Nat.mod_lt _ hn0) (by simp)
  have hab := next_ne n i (by omega) hi
  by_cases hbc : (i+1)%n=j
  · have had := next_next_ne n i hn hi
    rw [hbc] at had
    have hbd := next_ne n j (by omega) hj
    have hnodup : [i,j,(j+1)%n].Nodup := by simp [List.nodup_cons,Ne.symm had,Ne.symm hbd,show i≠j by omega]
    have hs : [i,j,(j+1)%n] ⊆ P := by
      intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    exact hnodup.length_le_of_subset hs
  · have hnodup : [i,(i+1)%n,j].Nodup := by simp [List.nodup_cons,Ne.symm hab,hbc,show i≠j by omega]
    have hs : [i,(i+1)%n,j] ⊆ P := by
      intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    exact hnodup.length_le_of_subset hs

#print axioms retained_boundary_ge_three
#print axioms retained_query_le_six
end Nanuq.Restriction
