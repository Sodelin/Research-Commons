import CappedGridCross

namespace ResearchCommons.BranchBagProjection
open ResearchCommons.CappedGridCross

/-- Branch-set membership needs one cell per bag vertex, not one vertex per
cell. Multiple vertices may project to the same cell. -/
theorem width_from_branch_hits {V : Type} (n : Nat) (bag : List V)
    (cellOf : V → Option (Nat × Nat))
    (hit : ∀ i j, i < n → j < n →
      ∃ v ∈ bag, ∃ x, cellOf v = some x ∧ (x.1 = i ∨ x.2 = j)) :
    n ≤ bag.length := by
  have projected : ∀ i j, i < n → j < n →
      ∃ x ∈ bag.filterMap cellOf, x.1 = i ∨ x.2 = j := by
    intro i j hi hj
    obtain ⟨v,hv,x,hx,hcross⟩ := hit i j hi hj
    exact ⟨x,List.mem_filterMap.mpr ⟨v,hv,hx⟩,hcross⟩
  exact Nat.le_trans (crossHittingLowerBound n _ projected)
    (List.length_filterMap_le cellOf bag)

-- Collisions in the projection are allowed: two bag vertices can have one cell.
example : ([0,1] : List Nat).filterMap (fun _ => some ((0,0) : Nat × Nat)) =
    [(0,0),(0,0)] := rfl

#print axioms width_from_branch_hits
end ResearchCommons.BranchBagProjection
