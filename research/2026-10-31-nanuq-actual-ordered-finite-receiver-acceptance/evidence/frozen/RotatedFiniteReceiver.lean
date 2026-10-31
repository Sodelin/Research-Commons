import RootedTreeOrder
import FiniteEdgeBridge

/-! UNCOMPILED exact finite receiver after a documented short cyclic rotation.
Only WHOLE-root expose/swap is used, never internal associativity. -/
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction Nanuq.AdjacentCertificate

theorem rotate_whole_leaves (t : LTree) (hsize : 2≤t.leaves.length) :
    ∃ u : LTree, u.leaves=t.leaves.rotate 1 ∧
      ∀ a b c d, u.Witness [] a b c d ↔ t.Witness [] a b c d := by
  have hs : 2≤(t.leaves.filter (fun _ => true)).length := by simpa using hsize
  obtain ⟨x,rest,hfull,hlist,hw⟩ := restriction_representation (fun _ => true) t hs
  have hl : t.leaves=x::rest.leaves := by simpa using hlist
  refine ⟨.fork rest (.tip x),?_,?_⟩
  · rw [hl]
    simp only [LTree.leaves,List.rotate_cons_succ,List.rotate_zero]
  · intro a b c d
    exact (witness_fork_swap rest (.tip x) [] a b c d).trans
      (hw a b c d rfl rfl rfl rfl)

/-- Simultaneous finite Tree for every quartet query at the rotated exact list. -/
theorem rotated_finite_receiver (t : LTree) (hsize : 2≤t.leaves.length)
    (k : Nat) (hk : k≤1) :
    ∃ T : Tree, T.size=(t.leaves.rotate k).length-1 ∧
      ∀ (q : Quartet) (r a b c d : Nat), q.parts r=(a,b,c,d) → a≠b → c≠d →
        (t.Witness [] a b c d ↔
          ∃ e∈T.internalIntervals 1, edgeWitness (t.leaves.rotate k) e.1 e.2 q r=true) := by
  have hu : ∃ u : LTree, u.leaves=t.leaves.rotate k ∧
      ∀ a b c d, u.Witness [] a b c d ↔ t.Witness [] a b c d := by
    have hcases : k=0 ∨ k=1 := by omega
    rcases hcases with rfl | rfl
    · exact ⟨t,by simp,fun _ _ _ _ => Iff.rfl⟩
    · exact rotate_whole_leaves t hsize
  obtain ⟨u,hul,hw⟩ := hu
  have hs : 2≤(u.leaves.filter (fun _ => true)).length := by
    simpa only [List.filter_true,hul,List.length_rotate] using hsize
  obtain ⟨x,rest,hfull,hlist,hqueries⟩ := restriction_representation (fun _ => true) u hs
  have hl : t.leaves.rotate k=x::rest.leaves := by
    simpa only [List.filter_true,hul] using hlist
  refine ⟨rest.erase,?_,?_⟩
  · rw [erase_size rest hfull,hl,List.length_cons]
    omega
  · intro q r a b c d hparts hab hcd
    have hrep := hqueries a b c d rfl rfl rfl rfl
    rw [hl]
    exact ((hw a b c d).symm.trans hrep.symm).trans
      (whole_first_edgeWitness x rest hfull q r a b c d hparts hab hcd)

#print axioms rotated_finite_receiver
end Nanuq.GraphReceiver
