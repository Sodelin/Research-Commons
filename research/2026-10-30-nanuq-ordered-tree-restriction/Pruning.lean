import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

inductive LTree where
  | empty
  | tip (label : Nat)
  | fork (left right : LTree)
  deriving DecidableEq, Repr

def LTree.leaves : LTree → List Nat
  | .empty => []
  | .tip x => [x]
  | .fork a b => a.leaves ++ b.leaves

def Cut (left right : List Nat) (a b c d : Nat) : Prop :=
  (a ∈ left ∧ b ∈ left ∧ c ∈ right ∧ d ∈ right) ∨
  (a ∈ right ∧ b ∈ right ∧ c ∈ left ∧ d ∈ left)

/-- Includes all subtree cuts. Pendant/root cuts will be removed only after
proving they cannot witness four distinct queried labels. -/
def LTree.Witness (t : LTree) (outside : List Nat) (a b c d : Nat) : Prop :=
  match t with
  | .empty => False
  | .tip x => Cut [x] outside a b c d
  | .fork l r => Cut (l.leaves ++ r.leaves) outside a b c d ∨
      l.Witness (r.leaves ++ outside) a b c d ∨
      r.Witness (l.leaves ++ outside) a b c d

def LTree.join (l r : LTree) : LTree :=
  match l,r with
  | .empty,r => r
  | l,.empty => l
  | l,r => .fork l r

def LTree.prune (keep : Nat → Bool) : LTree → LTree
  | .empty => .empty
  | .tip x => if keep x then .tip x else .empty
  | .fork l r => (l.prune keep).join (r.prune keep)

theorem leaves_join (l r : LTree) : (l.join r).leaves = l.leaves ++ r.leaves := by
  cases l <;> cases r <;> simp [LTree.join,LTree.leaves]

theorem leaves_prune (keep : Nat → Bool) (t : LTree) :
    (t.prune keep).leaves = t.leaves.filter keep := by
  induction t with
  | empty => rfl
  | tip x => simp [LTree.prune,LTree.leaves]; split <;> simp_all [LTree.leaves]
  | fork l r hl hr => simp only [LTree.prune,leaves_join,hl,hr,LTree.leaves,List.filter_append]

theorem root_cut_witness (t : LTree) (outside : List Nat) (a b c d : Nat)
    (h : Cut t.leaves outside a b c d) : t.Witness outside a b c d := by
  cases t with
  | empty => simp [Cut,LTree.leaves] at h
  | tip x => exact h
  | fork l r => exact Or.inl h

theorem witness_join (l r : LTree) (outside : List Nat) (a b c d : Nat) :
    (l.join r).Witness outside a b c d ↔ (LTree.fork l r).Witness outside a b c d := by
  cases l with
  | empty =>
    simp only [LTree.join,LTree.Witness,LTree.leaves,List.nil_append,false_or]
    exact ⟨Or.inr, fun h => h.elim (root_cut_witness r outside a b c d) id⟩
  | tip x =>
    cases r with
    | empty =>
      simp only [LTree.join,LTree.Witness,LTree.leaves,List.append_nil,List.nil_append,or_false]
      exact ⟨Or.inl, fun h => h.elim id id⟩
    | tip y => rfl
    | fork r s => rfl
  | fork l m =>
    cases r with
    | empty =>
      simp only [LTree.join,LTree.Witness,LTree.leaves,List.append_nil,List.nil_append,or_false]
      constructor
      · exact Or.inr
      · intro h
        exact h.elim (fun h => Or.inl h) id
    | tip y => rfl
    | fork r s => rfl

 theorem cut_filter (keep : Nat → Bool) (left right : List Nat) (a b c d : Nat)
    (ha : keep a=true) (hb : keep b=true) (hc : keep c=true) (hd : keep d=true) :
    Cut (left.filter keep) (right.filter keep) a b c d ↔ Cut left right a b c d := by
  simp [Cut,List.mem_filter,ha,hb,hc,hd]

theorem witness_prune (keep : Nat → Bool) (t : LTree) (outside : List Nat) (a b c d : Nat)
    (ha : keep a=true) (hb : keep b=true) (hc : keep c=true) (hd : keep d=true) :
    (t.prune keep).Witness (outside.filter keep) a b c d ↔ t.Witness outside a b c d := by
  induction t generalizing outside with
  | empty => rfl
  | tip x =>
    by_cases hx : keep x = true
    · simp only [LTree.prune,hx,if_true,LTree.Witness]
      have hf : ([x] : List Nat).filter keep = [x] := by simp [hx]
      simpa only [hf] using cut_filter keep [x] outside a b c d ha hb hc hd
    · have hax : a ≠ x := by intro h; subst x; exact hx ha
      have hcx : c ≠ x := by intro h; subst x; exact hx hc
      simp [LTree.prune,hx,LTree.Witness,Cut,hax,hcx]
  | fork l r hl hr =>
    rw [LTree.prune,witness_join]
    simp only [LTree.Witness,leaves_prune,← List.filter_append]
    rw [cut_filter keep (l.leaves ++ r.leaves) outside a b c d ha hb hc hd,
      hl (r.leaves ++ outside),hr (l.leaves ++ outside)]

#print axioms witness_prune
#print axioms witness_join
#print axioms leaves_prune
end Nanuq.Restriction
