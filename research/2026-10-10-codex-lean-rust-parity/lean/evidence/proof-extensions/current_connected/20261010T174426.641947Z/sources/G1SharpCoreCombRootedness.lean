import G1SharpCoreCombDegrees

/-! Original root reaches every vertex and taxon of the accepted symbolic
all-n comb family. Paths use actual original edge IDs. -/
namespace G1SharpCoreCombRootedness
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1SharpCoreCombDefinition G1SharpCoreCombDegrees

lemma local_U (n : Nat) (i : Module n) : (graph n).DReach (.inl (i,0)) (.inl (i,1)) :=
  Relation.ReflTransGen.single ⟨(i,1),rfl,rfl⟩
lemma local_V (n : Nat) (i : Module n) : (graph n).DReach (.inl (i,0)) (.inl (i,2)) :=
  (local_U n i).tail ⟨(i,3),rfl,rfl⟩
lemma local_HL (n : Nat) (i : Module n) : (graph n).DReach (.inl (i,0)) (.inl (i,3)) :=
  Relation.ReflTransGen.single ⟨(i,0),rfl,rfl⟩
lemma local_HR (n : Nat) (i : Module n) : (graph n).DReach (.inl (i,0)) (.inl (i,4)) :=
  (local_U n i).tail ⟨(i,2),rfl,rfl⟩

lemma local_vertex (n : Nat) (i : Module n) (k : LocalVertex) :
    (graph n).DReach (.inl (i,0)) (.inl (i,k)) := by
  fin_cases k
  · exact .refl
  · exact local_U n i
  · exact local_V n i
  · exact local_HL n i
  · exact local_HR n i

theorem root_reaches_module (n : Nat) (hn : 4 ≤ n) (i : Module n) :
    (graph n).DReach (root n hn) (.inl (i,0)) := by
  have aux : ∀ m : Nat, ∀ h : m < n-1, (graph n).DReach (root n hn) (.inl (⟨m,h⟩,0)) := by
    intro m
    induction m with
    | zero => intro h; exact .refl
    | succ m ih =>
      intro h
      have hprev : m < n-1 := by omega
      let prev : Module n := ⟨m,hprev⟩
      have hr := (ih hprev).trans (local_HR n prev)
      have ht : (graph n).target (prev,7) = .inl (⟨m+1,h⟩,0) := by
        simp only [graph,target,Fin.val_ofNat,show (7:Nat)%8=7 from rfl]
        have hnext : prev.val+1 < n-1 := h
        rw [dif_pos hnext]
      exact hr.tail ⟨(prev,7),rfl,ht⟩
  exact aux i.val i.isLt

theorem original_rooted (n : Nat) (hn : 4 ≤ n) (v : Vertex n) : (graph n).DReach (root n hn) v := by
  cases v with
  | inl pair => exact (root_reaches_module n hn pair.1).trans (local_vertex n pair.1 pair.2)
  | inr x =>
    by_cases hx : x.val < n-1
    · let i : Module n := ⟨x.val,hx⟩
      have hr := (root_reaches_module n hn i).trans (local_HL n i)
      have ht : (graph n).target (i,6) = .inr x := by
        apply congrArg Sum.inr
        apply Fin.ext
        rfl
      exact hr.tail ⟨(i,6),rfl,ht⟩
    · let i : Module n := ⟨n-2,by omega⟩
      have hr := (root_reaches_module n hn i).trans (local_HR n i)
      have hlast : x.val = n-1 := by have hh := x.isLt; omega
      have hnext : ¬ i.val+1 < n-1 := by dsimp [i]; omega
      have ht : (graph n).target (i,7) = .inr x := by
        simp only [graph,target,Fin.val_ofNat,show (7:Nat)%8=7 from rfl]
        rw [dif_neg hnext]
        apply congrArg Sum.inr
        exact Fin.ext hlast.symm
      exact hr.tail ⟨(i,7),rfl,ht⟩

#print axioms original_rooted
end G1SharpCoreCombRootedness
