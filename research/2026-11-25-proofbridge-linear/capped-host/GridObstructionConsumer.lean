import CappedGridObstruction
open PopulationCounting ResearchCommons.CappedConnectedBags ResearchCommons.CappedGridObstruction

example {k : Nat} (p : InfiniteLabeledPopulation k k)
    (side : Nat) (large : k * fullRootCount p + 1 < side)
    (f : Nat → Nat → Nat)
    (hrow : ∀ r c, r < side → c+1 < side → Adj p (f r c) (f r (c+1)))
    (hcol : ∀ r c, r+1 < side → c < side → Adj p (f r c) (f (r+1) c))
    (inj : ∀ x y : Nat × Nat, x.1 < side ∧ x.2 < side → y.1 < side ∧ y.2 < side →
      f x.1 x.2 = f y.1 y.2 → x = y) : False :=
  no_large_grid p side large f hrow hcol inj

private def emptyModel : InfiniteLabeledPopulation 0 0 where
  edge := fun _ _ => none
  root := fun _ => false
  birth_order := by simp
  root_no_parents := by simp
  parent_of_label := by simp
  childSupport := fun _ => 0
  no_children_after := by simp
  child_cap := by simp
  rootSupport := 0
  no_roots_after := by simp

/-- This diagnostic model admits a one-cell grid, so the +1 cannot
be silently dropped from the general obstruction interface. -/
theorem boundary_control :
    (0 : Nat) * fullRootCount emptyModel < 1 ∧
    ∃ f : Nat → Nat → Nat,
      (∀ r c, r < 1 → c+1 < 1 → Adj emptyModel (f r c) (f r (c+1))) ∧
      (∀ r c, r+1 < 1 → c < 1 → Adj emptyModel (f r c) (f (r+1) c)) ∧
      (∀ x y : Nat × Nat, x.1 < 1 ∧ x.2 < 1 → y.1 < 1 ∧ y.2 < 1 →
        f x.1 x.2 = f y.1 y.2 → x = y) := by
  refine ⟨by simp,fun _ _ => 0, ?_, ?_, ?_⟩
  · intro _ _ _ h
    omega
  · intro _ _ h _
    omega
  · intro ⟨a,b⟩ ⟨c,d⟩ ⟨ha,hb⟩ ⟨hc,hd⟩ _
    apply Prod.ext <;> omega

#print axioms boundary_control
