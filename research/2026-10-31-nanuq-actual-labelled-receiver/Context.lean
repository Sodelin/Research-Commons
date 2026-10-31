import Encode
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction
variable {V : Type*}

theorem Context.frontier_perm {t u : BinarySyntax V} {out : List V}
    (h : Context t u out) : t.frontier.Perm (u.frontier ++ out) := by
  induction h with
  | here t => simp
  | left v l r u out h ih =>
    simpa only [BinarySyntax.frontier,List.append_assoc] using ih.append_right r.frontier
  | right v l r u out h ih =>
    exact (List.perm_append_comm).trans (by
      simpa only [List.append_assoc] using ih.append_right l.frontier)

theorem Context.eq_or_below {t u : BinarySyntax V} {out : List V}
    (h : Context t u out) : (t=u ∧ out=[]) ∨ Below t u := by
  induction h with
  | here t => exact Or.inl ⟨rfl,rfl⟩
  | left v l r u out h ih =>
    rcases ih with ⟨rfl,_⟩ | ih
    · exact Or.inr (.left v l r)
    · exact Or.inr (.inLeft v l r u ih)
  | right v l r u out h ih =>
    rcases ih with ⟨rfl,_⟩ | ih
    · exact Or.inr (.right v l r)
    · exact Or.inr (.inRight v l r u ih)

#print axioms Context.frontier_perm
end Nanuq.GraphReceiver
