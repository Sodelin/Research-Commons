import CyclicGaps
import Mathlib.Data.List.Rotate

/-! UNCOMPILED independent finite block-receiver work. No source-level
order premise is introduced; the actual-source join must derive its inputs. -/
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

/-- Rotate the actual list once; adjacency survives even when a=b. -/
theorem cyclicGap_rotate_one (xs : List Nat) (a b : Nat)
    (h : CyclicGap xs a b) : CyclicGap (xs.rotate 1) a b := by
  rcases h with ⟨pre,post,rfl⟩ | ⟨middle,rfl⟩
  · cases pre with
    | nil =>
      apply Or.inr
      refine ⟨post,?_⟩
      simp only [List.nil_append,List.rotate_cons_succ,List.rotate_zero,List.cons_append]
    | cons z pre =>
      apply Or.inl
      refine ⟨pre,post++[z],?_⟩
      simp only [List.cons_append,List.rotate_cons_succ,List.rotate_zero,List.append_assoc]
  · apply Or.inl
    refine ⟨middle,[],?_⟩
    simp only [List.rotate_cons_succ,List.rotate_zero,List.append_assoc,List.cons_append,
      List.nil_append,List.append_nil]

/-- Repeated-label wrap adjacency is impossible at a break between different
endpoint labels. The explicit list shape avoids any head/last default convention. -/
theorem cyclicGap_linear_of_distinct_ends (first last x : Nat) (middle : List Nat)
    (hne : first≠last) (h : CyclicGap (first::(middle++[last])) x x) :
    LinearGap (first::(middle++[last])) x x := by
  rcases h with h | ⟨ys,he⟩
  · exact h
  · have hfirst : first=x := by simpa using congrArg List.head? he
    have hlast : last=x := by
      have hh := congrArg List.getLast? he
      change ((first::middle)++[last]).getLast? = ((x::ys)++[x]).getLast? at hh
      simpa only [List.getLast?_concat,Option.some.injEq] using hh
    exact False.elim (hne (hfirst.trans hlast.symm))

#print axioms cyclicGap_rotate_one
#print axioms cyclicGap_linear_of_distinct_ends
end Nanuq.Restriction
