import EncodeWitness
import Mathlib.Data.List.Perm.Basic

/-! UNCOMPILED syntax-only moves. No transformed directed Represents claim.
Every whole-root move preserves encoded quartet witnesses for ALL label maps. -/
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction
variable {V : Type*}

theorem cut_left_membership_congr (l l' r : List Nat) (a b c d : Nat)
    (h : ∀ x, x∈l ↔ x∈l') : Cut l r a b c d ↔ Cut l' r a b c d := by
  simp only [Cut,h a,h b,h c,h d]

theorem witness_fork_swap (l r : LTree) (out : List Nat) (a b c d : Nat) :
    (LTree.fork l r).Witness out a b c d ↔
      (LTree.fork r l).Witness out a b c d := by
  simp only [LTree.Witness,LTree.leaves]
  have hc := cut_left_membership_congr (l.leaves++r.leaves) (r.leaves++l.leaves)
    out a b c d (by intro x; simp only [List.mem_append,or_comm])
  rw [hc]
  constructor <;> rintro (h|h|h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem witness_fork_left_congr (l l' r : LTree)
    (hleaves : ∀ x, x∈l.leaves ↔ x∈l'.leaves)
    (hw : ∀ out a b c d, l.Witness out a b c d ↔ l'.Witness out a b c d)
    (out : List Nat) (a b c d : Nat) :
    (LTree.fork l r).Witness out a b c d ↔
      (LTree.fork l' r).Witness out a b c d := by
  have hc := cut_left_membership_congr (l.leaves++r.leaves) (l'.leaves++r.leaves)
    out a b c d (by intro x; simp only [List.mem_append,hleaves x])
  have hr := witness_outside_congr r (l.leaves++out) (l'.leaves++out) a b c d
    (by intro x; simp only [List.mem_append,hleaves x])
  simp only [LTree.Witness,LTree.leaves]
  rw [hc,hw,hr]

/-- Focus a selected ORIGINAL occurrence through whole-root moves, carrying the
entire outside syntax as accumulator. No internal associativity is used. -/
theorem focus_left (l : BinarySyntax V) (a : V) (ha : a∈l.frontier)
    (root : V) (r : BinarySyntax V) :
    ∃ v rest, (.fork v (.tip a) rest : BinarySyntax V).frontier.Perm
        (.fork root l r).frontier ∧
      ∀ (label : V → Nat) i j k m,
        (encode label (.fork v (.tip a) rest)).Witness [] i j k m ↔
          (encode label (.fork root l r)).Witness [] i j k m := by
  induction l generalizing root r with
  | tip x =>
    have hax : a=x := by simpa [BinarySyntax.frontier] using ha
    subst x
    exact ⟨root,r,List.Perm.refl _,fun _ _ _ _ _ => Iff.rfl⟩
  | fork v l s il ir =>
    rcases List.mem_append.mp ha with hal | has
    · obtain ⟨w,rest,hperm,hw⟩ := il hal v (.fork root s r)
      refine ⟨w,rest,?_,?_⟩
      · simpa only [BinarySyntax.frontier,List.append_assoc] using hperm
      · intro label i j k m
        exact (hw label i j k m).trans
          (whole_rotation (encode label l) (encode label s) (encode label r) i j k m).symm
    · obtain ⟨w,rest,hperm,hw⟩ := ir has v (.fork root l r)
      refine ⟨w,rest,?_,?_⟩
      · have hp : (s.frontier++l.frontier)++r.frontier ~
            (l.frontier++s.frontier)++r.frontier := List.perm_append_comm.append_right _
        exact hperm.trans (by simpa only [BinarySyntax.frontier,List.append_assoc] using hp)
      · intro label i j k m
        have hrot := (whole_rotation (encode label s) (encode label l)
          (encode label r) i j k m).symm
        have hflip := witness_fork_left_congr
          (.fork (encode label s) (encode label l))
          (.fork (encode label l) (encode label s)) (encode label r)
          (by intro x; simp only [LTree.leaves,List.mem_append,or_comm])
          (witness_fork_swap (encode label s) (encode label l)) [] i j k m
        exact (hw label i j k m).trans (hrot.trans hflip)

/-- The selected occurrence may lie on either side of the whole root. -/
theorem focus_occurrence (t : BinarySyntax V) (a : V) (ha : a∈t.frontier)
    (hsize : 2≤t.frontier.length) :
    ∃ v rest, (.fork v (.tip a) rest : BinarySyntax V).frontier.Perm t.frontier ∧
      ∀ (label : V → Nat) i j k m,
        (encode label (.fork v (.tip a) rest)).Witness [] i j k m ↔
          (encode label t).Witness [] i j k m := by
  cases t with
  | tip x => simp [BinarySyntax.frontier] at hsize
  | fork root l r =>
    rcases List.mem_append.mp ha with hal | har
    · exact focus_left l a hal root r
    · obtain ⟨v,rest,hperm,hw⟩ := focus_left r a har root l
      refine ⟨v,rest,hperm.trans List.perm_append_comm,?_⟩
      intro label i j k m
      exact (hw label i j k m).trans
        (witness_fork_swap (encode label r) (encode label l) [] i j k m)

#print axioms focus_occurrence
end Nanuq.GraphReceiver
