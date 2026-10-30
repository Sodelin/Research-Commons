import RootRotation
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

def LTree.Full : LTree → Prop
  | .empty => False
  | .tip _ => True
  | .fork l r => l.Full ∧ r.Full

def LTree.expose : LTree → LTree → LTree
  | .empty,r => .fork .empty r
  | .tip x,r => .fork (.tip x) r
  | .fork a b,r => a.expose (.fork b r)

theorem expose_leaves (l r : LTree) : (l.expose r).leaves = l.leaves ++ r.leaves := by
  induction l generalizing r with
  | empty => rfl
  | tip x => rfl
  | fork a b ha hb => simp only [LTree.expose,ha,LTree.leaves,List.append_assoc]

theorem expose_witness (l r : LTree) (a b c d : Nat) :
    (l.expose r).Witness [] a b c d ↔ (LTree.fork l r).Witness [] a b c d := by
  induction l generalizing r with
  | empty => rfl
  | tip x => rfl
  | fork l m hl hm =>
    exact (hl (LTree.fork m r)).trans (whole_rotation l m r a b c d).symm

theorem expose_first (l r : LTree) (hl : l.Full) (hr : r.Full) :
    ∃ x rest, rest.Full ∧ l.expose r = LTree.fork (.tip x) rest := by
  induction l generalizing r with
  | empty => exact False.elim hl
  | tip x => exact ⟨x,r,hr,rfl⟩
  | fork l m ih ih2 => exact ih (LTree.fork m r) hl.1 ⟨hl.2,hr⟩

theorem reduced_join (l r : LTree) (hl : l = .empty ∨ l.Full) (hr : r = .empty ∨ r.Full) :
    l.join r = .empty ∨ (l.join r).Full := by
  cases l <;> cases r <;> simp_all [LTree.join,LTree.Full]

theorem prune_reduced (keep : Nat → Bool) (t : LTree) :
    t.prune keep = .empty ∨ (t.prune keep).Full := by
  induction t with
  | empty => exact Or.inl rfl
  | tip x => cases hk : keep x <;> simp [LTree.prune,hk,LTree.Full]
  | fork l r hl hr => exact reduced_join _ _ hl hr

/-- A simultaneous representation for all retained quartet queries. The
choice of root/rest depends only on the pruned tree, not on the quartet. -/
theorem restriction_representation (keep : Nat → Bool) (t : LTree)
    (hsize : 2 ≤ (t.leaves.filter keep).length) :
    ∃ x rest, rest.Full ∧ t.leaves.filter keep = x :: rest.leaves ∧
      ∀ a b c d, keep a=true → keep b=true → keep c=true → keep d=true →
        ((LTree.fork (.tip x) rest).Witness [] a b c d ↔ t.Witness [] a b c d) := by
  have hred := prune_reduced keep t
  have hleaves := leaves_prune keep t
  cases htree : t.prune keep with
  | empty => simp only [htree,LTree.leaves] at hleaves; rw [← hleaves] at hsize; simp at hsize
  | tip x => simp only [htree,LTree.leaves] at hleaves; rw [← hleaves] at hsize; simp at hsize
  | fork l r =>
    rw [htree] at hred
    have hfull : l.Full ∧ r.Full := by simpa [LTree.Full] using hred
    obtain ⟨x,rest,hrest,he⟩ := expose_first l r hfull.1 hfull.2
    refine ⟨x,rest,hrest,?_,?_⟩
    · have heL := expose_leaves l r
      rw [he] at heL
      have hL : l.leaves ++ r.leaves = t.leaves.filter keep := by simpa only [htree,LTree.leaves] using hleaves
      simpa only [LTree.leaves,List.singleton_append] using hL.symm.trans heL.symm
    · intro a b c d ha hb hc hd
      have hp := witness_prune keep t [] a b c d ha hb hc hd
      simp only [List.filter_nil,htree] at hp
      rw [← he]
      exact (expose_witness l r a b c d).trans hp

#print axioms restriction_representation
#print axioms expose_witness
end Nanuq.Restriction
