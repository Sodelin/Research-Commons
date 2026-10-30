import CyclicGaps
import TreeEdgeSemantics
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

def LTree.erase : LTree → Tree
  | .empty => .tip
  | .tip _ => .tip
  | .fork l r => .fork l.erase r.erase

theorem erase_size (t : LTree) (h : t.Full) : t.erase.size = t.leaves.length := by
  induction t with
  | empty => exact False.elim h
  | tip x => rfl
  | fork l r hl hr => simp only [LTree.erase,Tree.size,LTree.leaves,List.length_append,hl h.1,hr h.2]

def intervalCut (tips : List Nat) (lo len a b c d : Nat) : Prop :=
  Cut ((tips.drop lo).take len) (tips.take lo ++ tips.drop (lo+len)) a b c d

theorem intervalCut_middle (pre mid post : List Nat) (a b c d : Nat) :
    intervalCut (pre++mid++post) pre.length mid.length a b c d ↔ Cut mid (pre++post) a b c d := by
  have hleft : (((pre++mid)++post).drop pre.length).take mid.length = mid := by
    rw [List.append_assoc,List.drop_left,List.take_left]
  have hpre : ((pre++mid)++post).take pre.length = pre := by
    rw [List.append_assoc,List.take_left]
  have hpost : ((pre++mid)++post).drop (pre.length+mid.length) = post := by
    rw [← List.length_append,List.drop_left]
  simp only [intervalCut,hleft,hpre,hpost]

theorem cut_tip_false (x : Nat) (outside : List Nat) (a b c d : Nat)
    (hab : a≠b) (hcd : c≠d) : ¬Cut [x] outside a b c d := by
  rintro (⟨ha,hb,hc,hd⟩ | ⟨ha,hb,hc,hd⟩)
  · exact hab ((List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm)
  · exact hcd ((List.mem_singleton.mp hc).trans (List.mem_singleton.mp hd).symm)

def hasInterval (t : Tree) (tips : List Nat) (lo a b c d : Nat) : Prop :=
  ∃ e∈t.internalIntervals lo, intervalCut tips e.1 e.2 a b c d

theorem hasInterval_fork (l r : Tree) (tips : List Nat) (lo a b c d : Nat) :
    hasInterval (.fork l r) tips lo a b c d ↔
      hasInterval l tips lo a b c d ∨ hasInterval r tips (lo+l.size) a b c d ∨
      intervalCut tips lo (l.size+r.size) a b c d := by
  simp only [hasInterval,Tree.internalIntervals,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    or_and_right,exists_or,exists_eq_left,or_assoc]

 theorem witness_intervals (t : LTree) (hf : t.Full) (pre post : List Nat) (a b c d : Nat)
    (hab : a≠b) (hcd : c≠d) :
    t.Witness (pre++post) a b c d ↔
      hasInterval t.erase (pre++t.leaves++post) pre.length a b c d := by
  induction t generalizing pre post with
  | empty => exact False.elim hf
  | tip x =>
    simp only [LTree.Witness,LTree.erase,hasInterval,Tree.internalIntervals,List.not_mem_nil,false_and,exists_false]
    exact iff_false_intro (cut_tip_false x (pre++post) a b c d hab hcd)
  | fork l r hl hr =>
    have hL := hl hf.1 pre (r.leaves++post)
    have hR := hr hf.2 (pre++l.leaves) post
    have cL := witness_outside_congr l (r.leaves++(pre++post)) (pre++(r.leaves++post)) a b c d
      (by intro x; simp only [List.mem_append,or_comm,or_left_comm,or_assoc])
    have cR := witness_outside_congr r (l.leaves++(pre++post)) ((pre++l.leaves)++post) a b c d
      (by intro x; simp only [List.mem_append,or_comm,or_left_comm,or_assoc])
    have hl' := cL.trans hL
    have hr' := cR.trans hR
    simp only [List.append_assoc,List.length_append] at hl' hr'
    simp only [LTree.Witness,LTree.erase,LTree.leaves,hasInterval_fork]
    rw [erase_size l hf.1,erase_size r hf.2]
    have hm := intervalCut_middle pre (l.leaves++r.leaves) post a b c d
    simp only [List.length_append,List.append_assoc] at hm
    simp only [List.append_assoc] at *
    rw [← hl',← hr',hm]
    simp only [or_comm,or_left_comm,or_assoc]

#print axioms witness_intervals
end Nanuq.Restriction
