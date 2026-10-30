import CanonicalRestriction
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

def LinearGap (xs : List Nat) (a b : Nat) : Prop :=
  ∃ pre post, xs = pre ++ a :: b :: post

def WrapGap (xs : List Nat) (a b : Nat) : Prop :=
  ∃ middle, xs = b :: (middle ++ [a])

def CyclicGap (xs : List Nat) (a b : Nat) : Prop := LinearGap xs a b ∨ WrapGap xs a b

theorem gap_filter (xs : List Nat) (keep : Nat → Bool) (a b : Nat)
    (h : CyclicGap xs a b) (ha : keep a=true) (hb : keep b=true) :
    CyclicGap (xs.filter keep) a b := by
  rcases h with ⟨pre,post,rfl⟩ | ⟨middle,rfl⟩
  · exact Or.inl ⟨pre.filter keep,post.filter keep,by simp [List.filter_append,ha,hb]⟩
  · exact Or.inr ⟨middle.filter keep,by simp [List.filter_append,ha,hb]⟩

theorem gap_map (xs : List Nat) (f : Nat → Nat) (a b : Nat) (h : CyclicGap xs a b) :
    CyclicGap (xs.map f) (f a) (f b) := by
  rcases h with ⟨pre,post,rfl⟩ | ⟨middle,rfl⟩
  · exact Or.inl ⟨pre.map f,post.map f,by simp [List.map_append]⟩
  · exact Or.inr ⟨middle.map f,by simp [List.map_append]⟩

theorem gap_range_next (n a b : Nat) (h : CyclicGap (List.range n) a b) :
    a<n ∧ b<n ∧ b=(a+1)%n := by
  rcases h with ⟨pre,post,h⟩ | ⟨middle,h⟩
  · have hlen := congrArg List.length h
    simp only [List.length_range,List.length_append,List.length_cons] at hlen
    have hi : pre.length<n := by omega
    have hj : pre.length+1<n := by omega
    have ha := congrArg (fun xs : List Nat => xs[pre.length]?) h
    rw [List.getElem?_range hi,List.getElem?_append_right (Nat.le_refl _)] at ha
    simp only [Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at ha
    have hb := congrArg (fun xs : List Nat => xs[pre.length+1]?) h
    rw [List.getElem?_range hj,List.getElem?_append_right (by omega)] at hb
    simp only [Nat.add_sub_cancel_left,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hb
    refine ⟨by omega,by omega,?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have hlen := congrArg List.length h
    simp only [List.length_range,List.length_append,List.length_cons,List.length_nil] at hlen
    have hb := congrArg (fun xs : List Nat => xs[0]?) h
    rw [List.getElem?_range (by omega)] at hb
    simp only [List.getElem?_cons_zero,Option.some.injEq] at hb
    have ha := congrArg (fun xs : List Nat => xs[middle.length+1]?) h
    rw [List.getElem?_range (by omega)] at ha
    simp only [List.getElem?_cons_succ,List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at ha
    refine ⟨by omega,by omega,?_⟩
    have han : a+1=n := by omega
    rw [han,Nat.mod_self]
    omega

theorem range_gap (n i : Nat) (hn : 2≤n) (hi : i<n) :
    CyclicGap (List.range n) i ((i+1)%n) := by
  by_cases h : i+1<n
  · rw [Nat.mod_eq_of_lt h]
    refine Or.inl ⟨List.range i,(List.range (n-(i+2))).map ((i+2)+·),?_⟩
    have he : n=(i+2)+(n-(i+2)) := by omega
    calc
      List.range n = List.range (i+2) ++ (List.range (n-(i+2))).map ((i+2)+·) := by
        conv_lhs => rw [he]
        exact List.range_add
      _ = _ := by simp only [List.range_succ,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
  · have he : i+1=n := by omega
    rw [he,Nat.mod_self]
    refine Or.inr ⟨(List.range (i-1)).map Nat.succ,?_⟩
    have hi1 : i=(i-1)+1 := by omega
    calc
      List.range n = List.range i ++ [i] := by rw [← he,List.range_succ]
      _ = _ := by
        conv_lhs => rw [hi1,List.range_succ_eq_map]
        simp only [List.cons_append,← hi1]

 theorem retained_gap_next (n : Nat) (keep : Nat → Bool) (a b : Nat)
    (h : CyclicGap (List.range n) a b) (ha : keep a=true) (hb : keep b=true) :
    (retained n keep).idxOf b = ((retained n keep).idxOf a+1)%(retained n keep).length := by
  have h1 := gap_filter (List.range n) keep a b h ha hb
  have h2 := gap_map (retained n keep) (retained n keep).idxOf a b h1
  have hn : (retained n keep).Nodup := (List.nodup_range (n:=n)).filter keep
  rw [map_idxOf_nodup (retained n keep) hn] at h2
  exact (gap_range_next _ _ _ h2).2.2

#print axioms retained_gap_next
#print axioms range_gap
end Nanuq.Restriction
