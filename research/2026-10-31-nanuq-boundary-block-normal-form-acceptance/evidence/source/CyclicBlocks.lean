import LinearBlocks

/-! UNCOMPILED. A cyclic list of singleton/double labels has a block break
without an arbitrary reorder: the original break or exactly one rotation. -/
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

/-- At most two copies of each label and at least two distinct labels guarantee
that either the original break or its one-step shift has unequal end labels. -/
theorem exists_distinct_end_break (xs : List Nat)
    (hcount : ∀ x, xs.count x≤2)
    (hdist : ∃ a∈xs, ∃ b∈xs, a≠b) :
    ∃ k first middle last, k≤1 ∧
      xs.rotate k=first::(middle++[last]) ∧ first≠last := by
  classical
  cases xs with
  | nil => simpa using hdist
  | cons x tail =>
    rcases List.eq_nil_or_concat' tail with rfl | ⟨middle,last,rfl⟩
    · obtain ⟨a,ha,b,hb,hab⟩ := hdist
      simp only [List.mem_singleton] at ha hb
      exact False.elim (hab (ha.trans hb.symm))
    · by_cases hxl : x=last
      · subst last
        cases middle with
        | nil =>
          obtain ⟨a,ha,b,hb,hab⟩ := hdist
          have ha' : a=x := by simpa using ha
          have hb' : b=x := by simpa using hb
          exact False.elim (hab (ha'.trans hb'.symm))
        | cons y ys =>
          have hyx : y≠x := by
            intro he
            subst y
            have hc := hcount x
            simp only [List.cons_append,List.count_cons_self,List.count_append,
              List.count_singleton_self] at hc
            omega
          refine ⟨1,y,ys++[x],x,by omega,?_,hyx⟩
          simp only [List.cons_append,List.rotate_cons_succ,List.rotate_zero,List.append_assoc]
      · exact ⟨0,x,middle,last,by omega,by simp,hxl⟩

/-- Exact blocks, retaining the original cyclic occurrence order. This finite
lemma does not itself supply a source-tree planar syntax or a global taxon order. -/
theorem cyclic_blocks_factor (xs : List Nat)
    (hcount : ∀ x, xs.count x≤2)
    (hdist : ∃ a∈xs, ∃ b∈xs, a≠b)
    (hpairs : ∀ x, xs.count x=2 → CyclicGap xs x x) :
    ∃ k base dup, k≤1 ∧ base.Nodup ∧ xs.rotate k=blocks base dup := by
  classical
  obtain ⟨k,first,middle,last,hk,he,hn⟩ := exists_distinct_end_break xs hcount hdist
  have hperm := List.rotate_perm xs k
  have hc : ∀ x, (xs.rotate k).count x≤2 := by
    intro x
    rw [hperm.count_eq]
    exact hcount x
  have hp : ∀ x, (xs.rotate k).count x=2 → LinearGap (xs.rotate k) x x := by
    intro x hx
    have hx' : xs.count x=2 := by simpa only [hperm.count_eq] using hx
    have hg : CyclicGap (xs.rotate k) x x := by
      have h := hpairs x hx'
      have hk' : k=0 ∨ k=1 := by omega
      rcases hk' with rfl | rfl
      · simpa using h
      · exact cyclicGap_rotate_one xs x x h
    rw [he] at hg ⊢
    exact cyclicGap_linear_of_distinct_ends first last x middle hn hg
  obtain ⟨base,dup,hnd,hblocks⟩ := linear_blocks_factor (xs.rotate k) hc hp
  exact ⟨k,base,dup,hk,hnd,hblocks⟩

#print axioms cyclic_blocks_factor
end Nanuq.Restriction
