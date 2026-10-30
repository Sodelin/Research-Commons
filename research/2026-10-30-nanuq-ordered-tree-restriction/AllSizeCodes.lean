import CoefficientTransport
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

theorem all_size_query_code_valid (n mask : Nat) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (x y p z : Nat) (hx : x<n) (hy : y<n) (hp : p<n) (hz : z<n)
    (hxy : x≠y) (hxp : x≠p) (hxz : x≠z) (hyp : y≠p) (hyz : y≠z) (hpz : p≠z) :
    code (codedPattern T (occurrenceLabels n mask) n) (quartetIndex (quartets n) x y p z) ∈
      ([1,4,5] : List Nat) := by
  let keep := queryKeep x y p z x y
  have hX : x∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hx (by simp)
  have hY : y∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hy (by simp)
  have hP : p∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hp (by simp)
  have hZ : z∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hz (by simp)
  have hnd : [x,y,p,z].Nodup := by simp [List.nodup_cons,hxy,hxp,hxz,hyp,hyz,hpz]
  have hsub : [x,y,p,z] ⊆ retained n keep := by
    intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> assumption
  have hfour := hnd.length_le_of_subset hsub
  have hcount : 3≤(retained n keep).length ∧ (retained n keep).length≤6 :=
    ⟨by simpa using Nat.le_trans (by decide : 3≤4) hfour,retained_query_le_six n x y p z x y⟩
  obtain ⟨newMask,U,hbound,hsize,hcheck,ht⟩ := construct_transport n mask keep T (by omega) hs hcount
  have htrans := query_transport n keep T U (occurrenceLabels n mask)
    (occurrenceLabels (retained n keep).length newMask) ht x y p z hX hY hP hZ hxy hxp hxz hyp hyz hpz
  rw [htrans.1]
  apply code_valid_of_check _ _ _ hcheck
  apply query_valid_of_check _ (bounded_queries _ hcount) _ _ _ _
    (List.idxOf_lt_length_iff.mpr hX) (List.idxOf_lt_length_iff.mpr hY)
    (List.idxOf_lt_length_iff.mpr hP) (List.idxOf_lt_length_iff.mpr hZ)
  exact ⟨fun h=>hxy ((List.idxOf_inj hX).mp h),
    fun h=>hxp ((List.idxOf_inj hX).mp h),fun h=>hxz ((List.idxOf_inj hX).mp h),
    fun h=>hyp ((List.idxOf_inj hY).mp h),fun h=>hyz ((List.idxOf_inj hY).mp h),
    fun h=>hpz ((List.idxOf_inj hP).mp h)⟩

#print axioms all_size_query_code_valid
end Nanuq.Restriction
