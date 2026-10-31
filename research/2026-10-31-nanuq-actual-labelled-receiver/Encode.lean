import GraphFrontier
import Reroot
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction
variable {V : Type*}

def encode (label : V → Nat) : BinarySyntax V → LTree
  | .tip v => .tip (label v)
  | .fork _ l r => .fork (encode label l) (encode label r)

theorem encode_leaves (label : V → Nat) (t : BinarySyntax V) :
    (encode label t).leaves = t.frontier.map label := by
  induction t with
  | tip v => rfl
  | fork v l r il ir => simp [encode,LTree.leaves,BinarySyntax.frontier,il,ir]

theorem encode_full (label : V → Nat) (t : BinarySyntax V) : (encode label t).Full := by
  induction t with
  | tip v => trivial
  | fork v l r il ir => exact ⟨il,ir⟩

/-- A subtree occurrence with its actual outside terminal occurrences.
Occurrences, not taxon labels, are kept separate until the final map. -/
inductive Context : BinarySyntax V → BinarySyntax V → List V → Prop where
  | here (t) : Context t t []
  | left (v) (l r u) (out) : Context l u out → Context (.fork v l r) u (out ++ r.frontier)
  | right (v) (l r u) (out) : Context r u out → Context (.fork v l r) u (out ++ l.frontier)

theorem below_context {t u : BinarySyntax V} (h : Below t u) :
    ∃ out, Context t u out := by
  induction h with
  | left v l r => exact ⟨[]++r.frontier,.left v l r l [] (.here l)⟩
  | right v l r => exact ⟨[]++l.frontier,.right v l r r [] (.here r)⟩
  | inLeft v l r u h ih =>
    obtain ⟨out,ho⟩ := ih
    exact ⟨out++r.frontier,.left v l r u out ho⟩
  | inRight v l r u h ih =>
    obtain ⟨out,ho⟩ := ih
    exact ⟨out++l.frontier,.right v l r u out ho⟩
end Nanuq.GraphReceiver
