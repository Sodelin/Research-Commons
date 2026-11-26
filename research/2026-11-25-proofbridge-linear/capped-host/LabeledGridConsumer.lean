import CappedLabeledGrid
open ResearchCommons.CappedLabeledGrid

example {n k : Nat} (v : Vertex n k) :
    ∃ xs : List (Vertex n k), xs.length ≤ 2 ∧
      ∀ w l, edge v w = some l → w ∈ xs :=
  children_covered v

private def a : Cell 2 := (0,0)
private def b : Cell 2 := (0,1)
-- Interior west edges use label 0, so its private pad root is disabled.
theorem no_extra_west_parent : @edge 2 2 (.inl (b,0)) (.inr b) = none := by decide
theorem real_west_parent : @edge 2 2 (.inr a) (.inr b) = some 0 := by decide
theorem boundary_private_parent : @edge 2 2 (.inl (a,0)) (.inr a) = some 0 := by decide

#print axioms no_extra_west_parent
#print axioms boundary_private_parent
