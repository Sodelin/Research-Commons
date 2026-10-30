import Pruning
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

theorem cut_right_congr (left r s : List Nat) (a b c d : Nat)
    (h : ∀ x, x∈r ↔ x∈s) : Cut left r a b c d ↔ Cut left s a b c d := by
  simp only [Cut,h a,h b,h c,h d]

theorem witness_outside_congr (t : LTree) (r s : List Nat) (a b c d : Nat)
    (h : ∀ x, x∈r ↔ x∈s) : t.Witness r a b c d ↔ t.Witness s a b c d := by
  induction t generalizing r s with
  | empty => rfl
  | tip x => exact cut_right_congr [x] r s a b c d h
  | fork l t hl ht =>
    simp only [LTree.Witness]
    rw [cut_right_congr _ r s a b c d h]
    have h1 : ∀ x, x∈t.leaves++r ↔ x∈t.leaves++s := by intro x; simp only [List.mem_append,h x]
    have h2 : ∀ x, x∈l.leaves++r ↔ x∈l.leaves++s := by intro x; simp only [List.mem_append,h x]
    rw [hl _ _ h1,ht _ _ h2]

theorem cut_swap (l r : List Nat) (a b c d : Nat) : Cut l r a b c d ↔ Cut r l a b c d := by
  simp only [Cut,or_comm]

theorem whole_fork (l r : LTree) (a b c d : Nat) :
    (LTree.fork l r).Witness [] a b c d ↔
      l.Witness r.leaves a b c d ∨ r.Witness l.leaves a b c d := by
  simp [LTree.Witness,Cut]

/-- Only the WHOLE root is rotated. No invariance of internal associativity
is asserted: an external context would change the represented split. -/
theorem whole_rotation (A B C : LTree) (a b c d : Nat) :
    (LTree.fork (LTree.fork A B) C).Witness [] a b c d ↔
      (LTree.fork A (LTree.fork B C)).Witness [] a b c d := by
  rw [whole_fork,whole_fork]
  simp only [LTree.Witness,LTree.leaves]
  have hB := witness_outside_congr B (C.leaves++A.leaves) (A.leaves++C.leaves) a b c d
    (by intro x; simp only [List.mem_append,or_comm])
  have hC := witness_outside_congr C (B.leaves++A.leaves) (A.leaves++B.leaves) a b c d
    (by intro x; simp only [List.mem_append,or_comm])
  rw [hB,hC]
  constructor
  · rintro ((h | h | h) | h)
    · exact Or.inr (Or.inr (Or.inr (root_cut_witness C _ a b c d ((cut_swap _ _ a b c d).mp h))))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inl (root_cut_witness A _ a b c d ((cut_swap _ _ a b c d).mp h))))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr h

#print axioms whole_rotation
end Nanuq.Restriction
